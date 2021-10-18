package fos

import scala.util.parsing.input.Positional
import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.Reader
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition


/** Abstract Syntax Trees for terms. */
sealed abstract class Term extends Positional
case object True extends Term
case object False extends Term
case class If(cond: Term, t1: Term, t2: Term) extends Term
case object Zero extends Term
case class Succ(t: Term) extends Term
case class Pred(t: Term) extends Term
case class IsZero(t: Term) extends Term

// // Tokens
// sealed trait WorkflowToken

// case object TRUE extends WorkflowToken
// case object FALSE extends WorkflowToken
// case object IF extends WorkflowToken
// case object THEN extends WorkflowToken
// case object ELSE extends WorkflowToken
// case class NUMBER(num: Int) extends WorkflowToken
// case object SUCC extends WorkflowToken
// case object PRED extends WorkflowToken
// case object ISZERO extends WorkflowToken
// case object ZERO extends WorkflowToken


// object Lexer extends RegexParsers {
//     override def skipWhitespace = true
//     override val whiteSpace = "[ \t\r\f]+".r

//     def trueTerm = "true" ^^(_=>TRUE)
//     def falseTerm = "false" ^^(_=>FALSE)
//     def zero = "0" ^^(_=>ZERO)
//     def succ = "succ" ^^(_=>SUCC)
//     def pred = "pred" ^^(_=>PRED)
//     def ifTerm = "if" ^^(_=>IF)
//     def isZero = "iszero" ^^(_=>ISZERO)
//     def thenTerm = "then" ^^(_=>THEN)
//     def elseTerm = "else" ^^(_=>ELSE)
//     def number: Parser[NUMBER] = {"[1-9]".r} ^^{str => NUMBER(str.toInt)}

//     def tokens: Parser[List[WorkflowToken]] = {phrase(rep1(trueTerm | falseTerm | zero | succ | pred | ifTerm | isZero
//      | thenTerm | elseTerm | number))}

//     trait WorkflowCompilationError
//     case class WorkflowLexerError(msg: String) extends WorkflowCompilationError
    
//     def apply(code: String): Either[WorkflowLexerError, List[WorkflowToken]] = {
//     parse(tokens, code) match {
//       case NoSuccess(msg, next) => Left(WorkflowLexerError(msg))
//       case Success(result, next) => Right(result)
//     }}
    
//     def main(args: Array[String]) = println(apply("if iszero pred pred then 2 if iszero 0 then true else false else false"))

// }


// object Parser extends Parsers{
//     override type Elem = Term
//     class WorkflowTokenReader(tokens: Seq[WorkflowToken]) extends Reader[WorkflowToken] {
//     override def first: WorkflowToken = tokens.head
//     override def atEnd: Boolean = tokens.isEmpty
//     override def pos: Position = NoPosition
//     override def rest: Reader[WorkflowToken] = new WorkflowTokenReader(tokens.tail)
//     }

//     def terms: Parser[Term] = {
//         val ifthen = IF~terms~THEN~terms~ELSE~terms ^^{case "if"~t1~"then"~t2~"else"~t3 => If(t1,t2,t3)}
//         val succ = SUCC~terms ^^{case "succ"~t => Succ(t)}
//         val pred = PRED~terms ^^{case "pred"~t => Pred(t)}
//         val iszero = ISZERO~terms ^^{case "iszero"~t => IsZero(t)}

//         ifthen|succ|pred|iszero|True|False|NUMBER
//     }

//     def nv: Parser[Term] = {
//         val zero = ZERO ^^{case ZERO => Zero}

//     }

//     def values: Parser[values] = {
        
//     }


   

// }