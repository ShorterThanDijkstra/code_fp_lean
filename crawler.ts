import axios from 'axios';
import { JSDOM } from 'jsdom';

const ROOT_CONTENTS_SELECTOR = "body > div > main > div > section > section > ol > li > a"
const CHAPTER_CONTENTS_SELECTOR = "body > div > main > div > section > ol > li > a"
const ROOT_URL = "https://lean-lang.org/functional_programming_in_lean/";

async function getPage(url: string): Promise<string> {
  try {
    const response = await axios.get(url);
    return response.data;
  } catch (error: any) {
    console.error("Error fetching the web page with axios:", error.message);
    throw error;
  }
}
type NameUrl = [string, string]
async function getRootUrls():Promise<NameUrl[]> {
    const page = await getPage(ROOT_URL);
    const dom = new JSDOM(page);
    const document = dom.window.document;
    const aTags = document.querySelectorAll(ROOT_CONTENTS_SELECTOR) as NodeListOf<HTMLAnchorElement>;
    const contentsHref = Array.from(aTags).map(it => ([it.text, `${ROOT_URL}${it.href}`] as NameUrl))
    return contentsHref;
}

// async function getChapterUrls(url: string):Promise<NameUrl[]> {
//     const page = await getPage(url);
//     return null;
    
// }
getRootUrls().then(data => console.log(data))