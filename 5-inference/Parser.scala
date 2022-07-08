package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

object Parser extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in")

  /** <pre>
   *  Term     ::= SimpleTerm { SimpleTerm }</pre>
   */
  def term: Parser[Term] = positioned(
    simpleTerm ~ rep(simpleTerm) ^^ { case t ~ ts => (t :: ts).reduceLeft[Term](App.apply) }
    | failure("illegal start of term"))

  /** <pre>
   *  SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident [":" Type] "." Term
   *               | "(" Term ")"
   *               | "let" ident [":" Type] "=" Term "in" Term</pre>
   */
  def simpleTerm: Parser[Term] = positioned(
      "true"          ^^^ True
    | "false"         ^^^ False
    | numericLit      ^^ { case chars => lit2Num(chars.toInt) }
    | "succ" ~ term   ^^ { case "succ" ~ t => Succ(t) }
    | "pred" ~ term   ^^ { case "pred" ~ t => Pred(t) }
    | "iszero" ~ term ^^ { case "iszero" ~ t => IsZero(t) }
    | "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^ {
        case "if" ~ t1 ~ "then" ~ t2 ~ "else" ~ t3 => If(t1, t2, t3)
      }
    | ident ^^ { case id => Var(id) }
    | "\\" ~ ident ~ opt(":" ~ typ) ~ "." ~ term ^^ {
      case "\\" ~ x ~ Some(":" ~ tp) ~ "." ~ t => Abs(x, tp, t)
      case "\\" ~ x ~ None ~ "." ~ t => Abs(x, EmptyTypeTree(), t)
    }
    | "(" ~> term <~ ")"  ^^ { case t => t }
    | "let" ~ ident ~ opt(":" ~ typ) ~ "=" ~ term ~ "in" ~ term ^^ {
      case "let" ~ x ~ Some(":" ~ tp) ~ "=" ~ t1 ~ "in" ~ t2 => Let(x, tp, t1, t2)
      case "let" ~ x ~ None ~ "=" ~ t1 ~ "in" ~ t2 => Let(x, EmptyTypeTree(), t1, t2)
    }
    | failure("illegal start of simple term"))

  /** <pre>
   *  Type       ::= SimpleType { "->" Type }</pre>
   */
  def typ: Parser[TypeTree] = positioned(
      baseType ~ opt("->" ~ typ) ^^ {
        case t1 ~ Some("->" ~ t2) => FunTypeTree(t1, t2)
        case t1 ~ None => t1
      }
    | failure("illegal start of type"))

  /** <pre>
   *  BaseType ::= "Bool" | "Nat" | "(" Type ")"</pre>
   */
  def baseType: Parser[TypeTree] = positioned(
      "Bool" ^^^ BoolTypeTree()
    | "Nat"  ^^^ NatTypeTree()
    | "(" ~> typ <~ ")" ^^ { case t => t }
  )

  private def lit2Num(n: Int): Term =
    if (n == 0) Zero else Succ(lit2Num(n - 1))
}
