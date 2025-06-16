import axios from 'axios';
import { JSDOM } from 'jsdom';
import * as fs from 'fs/promises';

const ROOT_CONTENTS_SELECTOR = "body > div > main > div > section > section > ol > li > a"
const CHAPTER_CONTENTS_SELECTOR = "body > div > main > div > section > ol > li > a"
const ROOT_URL = "https://lean-lang.org/functional_programming_in_lean/";
type NameUrl = { name: string, url: string }

async function parse() {
  const root = await parseRootPage();
  for (const chapter of root) {
    const sections = await parseChapterPage(chapter);
    await randomDelay(1000, 3000);
    for (const section of sections) {
      const codes = await parseSectionPage(section);
      await randomDelay(1000, 3000);
      saveCode(section, codes);
      return;
    }
  }
}

function randomDelay(min: number, max: number) {
    const ms = Math.random() * (max - min) + min;
    return new Promise(resolve => setTimeout(resolve, ms));
}

async function checkFileExists(filePath: string): Promise<boolean> {
  try {
    await fs.access(filePath, fs.constants.F_OK);
    return true;
  } catch (error) {
    return false;
  }
}

async function writeFile(filePath: string, content: string) {
  try {
    await fs.writeFile(filePath, content, 'utf8');
  } catch (err: any) {
    console.log(`写入文件失败：${filePath}`)
  }
  console.log(`写入文件成功：${filePath}`)
}

async function getPage(url: string): Promise<string> {
  try {
    const response = await axios.get(url);
    return response.data;
  } catch (error: any) {
    console.error("Error fetching the web page with axios:", error.message);
    throw error;
  }
}

async function parsePageNameUrls(nameUrl: NameUrl, selector: string) {
  const filePath = `./html/${nameUrl.name}.html`
  const fileExists = await checkFileExists(filePath)
  let page = ''
  if (fileExists) {
    page = await fs.readFile(filePath, 'utf8');
  } else {
    page = await getPage(nameUrl.url);
    fs.writeFile(filePath, page, 'utf8');
  }
  const dom = new JSDOM(page);
  const document = dom.window.document;
  const aTags = document.querySelectorAll(selector) as NodeListOf<HTMLAnchorElement>;
  const contentsHref = Array.from(aTags).map(it => ({ name: it.text.replace(/\s/g, ''), url: `${ROOT_URL}${it.href}` } as NameUrl))
  return contentsHref;
}

async function parseRootPage(): Promise<NameUrl[]> {
  return parsePageNameUrls({ name: "root", url: ROOT_URL }, ROOT_CONTENTS_SELECTOR);
}

async function parseChapterPage(nameUrl: NameUrl): Promise<NameUrl[]> {
  return parsePageNameUrls(nameUrl, CHAPTER_CONTENTS_SELECTOR);
}

async function parseSectionPage(nameUrl: NameUrl) {
  const filePath = `./html/${nameUrl.name}.html`
  const fileExists = await checkFileExists(filePath)
  let page = await getPage(nameUrl.url);

  if (fileExists) {
    page = await fs.readFile(filePath, 'utf8');
  } else {
    page = await getPage(nameUrl.url);
    writeFile(filePath, `${nameUrl.url}\n${page}`);
  }
  const dom = new JSDOM(page);
  const document = dom.window.document;
  const codeTags = document.querySelectorAll('code.hl.lean.block');
  const codes = Array.from(codeTags).map(it => it.textContent || '')
  return codes;
}

async function saveCode(nameUrl: NameUrl, codes: string[]) {
  const filePath = `./code/${nameUrl.name}.lean`;
  const content = `//${nameUrl.url}\n${codes.join("\n")}`
  writeFile(filePath, content);
}
parse()