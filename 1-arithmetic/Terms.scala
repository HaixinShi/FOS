package fos

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for terms. */
sealed abstract class Term extends Positional
case object True extends Term
case object False extends Term
case class If(cond: Term, t1: Term, t2: Term) extends Term
case object Zero extends Term
case class Succ(t: Term) extends Term
case class Pred(t: Term) extends Term
case class IsZero(t: Term) extends Term
