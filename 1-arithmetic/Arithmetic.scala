package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.*

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | numericLit
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] = ("if"~term~"then" ~term~ "else"~term^^{case "if"~cond~"then"~t1~"else"~t2=>If(cond,t1,t2)})|
    numericLit^^{
      case "0"=>Zero//I have no idea about how to recursively process a positive
      case "1"=>Succ(Zero)
      case "2"=>Succ(Succ(Zero))
      case "3"=>Succ(Succ(Succ(Zero)))
      case "4"=>Succ(Succ(Succ(Succ(Zero))))
      case "5"=>Succ(Succ(Succ(Succ(Succ(Zero)))))
      case "6"=>Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))
      case "7"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))
      case "8"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero))))))))
      case "9"=>Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Succ(Zero)))))))))
    }|
    "true"^^{_=>True}|
    "false"^^{_=>False}|
    ("iszero"~term^^{case "iszero"~expr=>IsZero(expr)})|
    "succ"~term^^{case "succ"~expr=>Succ(expr)}|
    "pred"~term^^{case "pred"~expr=>Pred(expr)}

   // note: you should use `numericLit` to parse numeric literals

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 7): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match {
    case True=>True
    case False=>False
    case Zero=>Zero
    case If(cond, t1, t2)=> cond match {
      case True=>t1
      case False=>t2
      case _=>If(reduce(cond),t1,t2)
    }
    case IsZero(expr)=>expr match {
      case Zero=>True
      case Succ(expr)=>False
      case _=>IsZero(reduce(expr))
    }

    case Pred(expr)=>expr match {
      case Zero=>Zero
      case False=>throw new NoReductionPossible(t)
      case True=>throw new NoReductionPossible(t)
      case Pred(Succ(expr))=>//the reduction time may be wrong
      try{
        reduce(expr)
      }
      catch {
        case NoReductionPossible(t)=>expr
      }
      case _=>Pred(reduce(expr))
    }
    case Succ(expr)=>expr match {
      case False => throw new NoReductionPossible(t)
      case True => throw new NoReductionPossible(t)
      case Zero => throw new NoReductionPossible(t)//in this case, there will be no reduction
      case _ => Succ(reduce(expr))
    }
    /*
    case Pred(Succ(expr))=>expr
    case Pred(Pred(expr))=>Pred(reduce(Pred(expr)))
    case Pred(Zero)=>Zero
    case _=>throw new NoReductionPossible(t)
  */
  }

  //How to define nv? (isZero succ nv → false)
  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term =t match{
    case True=>True
    case False=>False
    case Zero=>Zero
    case If(cond, t1, t2)=> cond match {
      case True=>eval(t1)
      case False=>eval(t2)
      case _=>eval(If(eval(cond),t1,t2))
    }
    case IsZero(expr)=>expr match {
      case Zero=>True
      case Succ(expr)=>False
      case _=>eval(IsZero(eval(expr)))
    }
    case Pred(Succ(expr))=>eval(expr)
    case Pred(Pred(expr))=>eval(Pred(eval(Pred(expr))))
    case Pred(Zero)=>Zero
    case Succ(expr)=> expr match {
      case False=>throw TermIsStuck(t)
      case True=>throw TermIsStuck(t)
      case _=>Succ(eval(expr))
    }
  }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
