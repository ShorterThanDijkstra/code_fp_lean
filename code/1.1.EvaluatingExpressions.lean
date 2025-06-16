//https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Evaluating-Expressions/#evaluating
3#eval 1 + 2
11#eval 1 + 2 * 5
"Hello, Lean!"#eval String.append "Hello, " "Lean!"
"great oak tree"#eval String.append "great " (String.append "oak " "tree")
String.append "it is " (if 1 > 2 then "yes" else "no")
String.append "it is " (if false then "yes" else "no")
String.append "it is " "no"
String.append "it is " (if 1 > 2 then "yes" else "no")
String.append "it is " (if false then "yes" else "no")
String.append "it is " "no"
"it is no"
could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  String → String#eval String.append "it is "