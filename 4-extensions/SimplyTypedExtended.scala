package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


  /** t ::=          "true"
   *               | "false"
   *               | number
   *               | "succ" t
   *               | "pred" t
   *               | "iszero" t
   *               | "if" t "then" t "else" t
   *               | ident
   *               | "\" ident ":" T "." t
   *               | t t
   *               | "(" t ")"
   *               | "let" ident ":" T "=" t "in" t
   *               | "{" t "," t "}"
   *               | "fst" t
   *               | "snd" t
   *               | "inl" t "as" T
   *               | "inr" t "as" T
   *               | "case" t "of" "inl" ident "=>" t "|" "inr" ident "=>" t
   *               | "fix" t
   *               | "letrec" ident ":" T "=" t "in" t
   */

  def termPrime: Parser[Term] = (
    "true" ^^ {case "true" => True}
      | "false" ^^ {case "false" => False}
      | "succ" ~ term ^^ {case "succ" ~ t => Succ(t)}
      | "pred" ~ term ^^ {case "pred" ~ t => Pred(t)}
      | "iszero" ~ term ^^ {case "iszero" ~ t => IsZero(t)}
      | ("if" ~ term ~ "then" ~ term ~ "else" ~ term ^^
      {case "if" ~ cond ~ "then" ~ t1 ~ "else" ~ t2 => If(cond, t1, t2)})
      | ident ^^ {case str => Var(str)}
      | ("\\" ~ ident ~ ":" ~ funcTypeTerm ~ "." ~ term ^^
      {case "\\" ~ v ~ ":" ~ tp ~ "." ~ t => Abs(v, tp, t)})
      | "(" ~ term ~ ")" ^^ {case "(" ~ t ~ ")" => t}
      | ("let" ~ ident ~ ":" ~ funcTypeTerm ~ "=" ~ term ~ "in" ~ term ^^
      {case "let" ~ v ~ ":" ~ tp ~ "=" ~ t1 ~ "in" ~ t2 => App(Abs(v, tp, t2), t1)})
      | ("{" ~ term ~ "," ~ term ~ "}" ^^
      {case "{" ~ t1 ~ "," ~ t2 ~ "}" => TermPair(t1, t2)})
      | "fst" ~ term ^^ {case "fst" ~ t => First(t)}
      | "snd" ~ term ^^ {case "snd" ~ t => Second(t)}
      | numericLit ^^ {case str => number2Str(str.toInt)}
      | "inl" ~ term ~ "as" ~ funcTypeTerm ^^ {case _ ~ t ~ _ ~ tp => Inl(t,tp)}
      | "inr" ~ term ~ "as" ~ funcTypeTerm ^^ {case _ ~ t ~ _ ~ tp => Inr(t,tp)}
      | ("case" ~ term ~ "of" ~ "inl" ~ ident ~ "=>" ~ term ~ "|" ~ "inr" ~ ident ~ "=>" ~ term ^^
      {case _ ~ t ~ _ ~ _ ~ str1 ~ "=>" ~ t1 ~ _ ~ _ ~ str2 ~ _ ~ t2 => Case(t, str1, t1, str2, t2)})
      | "fix" ~ term ^^ {case _ ~ t => Fix(t)}
      | ("letrec" ~ ident ~ ":" ~ funcTypeTerm ~ "=" ~ term ~ "in" ~ term ^^
      {case _ ~ str ~ _ ~ tp ~ _ ~ t1 ~ _ ~ t2 => App(Abs(str, tp, t2), Fix(Abs(str, tp, t1)))})
    )

  def number2Str(i: Int):Term = {
    var tmp:Term = Zero;
    for(i <- 1 to i)
      tmp = Succ(tmp)
    return tmp
  }

  def term: Parser[Term] = (
    termPrime ~ rep(termPrime) ^^ reduceList
    )

  val reduceList: Term ~ List[Term] => Term = {
    case t ~ tList => tList.foldLeft(t)(App(_,_))
  }

  def pairTypeTerm: Parser[Type] = (
    simpleTypeTerm ~ "*" ~ pairTypeTerm ^^ {case stp ~ _ ~ ptp => TypePair(stp,ptp)}
      | simpleTypeTerm ~ "+" ~ pairTypeTerm ^^ {case stp ~ _ ~ ptp => TypeSum(stp,ptp)}
      | simpleTypeTerm
    )

  def funcTypeTerm: Parser[Type] = repsep(pairTypeTerm, "->") ^^ {case tyList => tyList.reduceRight(TypeFun(_,_))}

  def simpleTypeTerm: Parser[Type] = (
  "Bool" ^^ {case "Bool" => TypeBool}
  | "Nat" ^^ {case "Nat" => TypeNat}
  | ("(" ~ funcTypeTerm ~ ")" ^^ {case "(" ~ tp ~ ")" => tp}))



  /** Call by value reducer. */
  def alpha(t: Abs): Abs = t match{
    case Abs(str, tp, term) => Abs(str+'0', tp, alphahelper(term, tp, str))
  }

  def alphahelper(t: Term, tp: Type, str: String): Term = t match{
    case Var(s) => if s == str then Var(str+'0') else Var(s)
    case Abs(s, tp, t) => if s == str then Abs(str+'0', tp, alphahelper(t, tp, str)) else Abs(s, tp, alphahelper(t, tp, str))
    case App(t1, t2) => App(alphahelper(t1, tp, str), alphahelper(t2, tp, str))
  }

  def calculateFv(t: Term): Set[Var] = {
    t match{
      case Var(str) => Set(Var(str))
      case Abs(str, tp, term) => {
        calculateFv(term).-(Var(str))}
      case App(t1, t2) => {
        calculateFv(t1).++(calculateFv(t2))
      }
      case Succ(t1) => calculateFv(t1)
      case Pred(t1) => calculateFv(t1)
      case IsZero(t1) => calculateFv(t1)
      case If(cond, t1, t2) =>{
        var tmp = calculateFv(t1)
        tmp = tmp ++ calculateFv(t2)
        tmp = tmp ++ (calculateFv(cond))
        tmp
      }

      case First(t1) => calculateFv(t1)
      case Second(t1) => calculateFv(t1)
      case TermPair(t1, t2) => calculateFv(t1).++(calculateFv(t2))

      case Case(t0: Term, x1: String, t1: Term, x2: String, t2: Term) =>{
        var tmp = calculateFv(t0)
        tmp = tmp ++ calculateFv(t1)
        tmp = tmp ++ (calculateFv(t2))
        tmp
      }
      case Inr(t0: Term, tpe: Type) =>calculateFv(t0)
      case Inl(t0: Term, tpe: Type) =>calculateFv(t0)
      case Fix(t0: Term) =>{
        calculateFv(t0)
      }

      case _ => Set()
    }}
  def subst(t: Term, x: String, s: Term): Term = {//[x->s]t
    t match {
      case Var(str) => if str == x then s else Var(str)
      case Abs(str, tp, term) =>  {//str = y, term = (\x:Nat.iszero x)
        str ==x match {//y != x
          case true => Abs(str, tp, term)
          case false => calculateFv(s).contains(Var(str)) match {
            case true => alpha(Abs(str, tp, term)) match {
              case Abs(str, tp, term) => Abs(str, tp, subst(term, x, s))
            }
            case false => Abs(str, tp, subst(term, x, s))
          }
        }}
      case App(t1, t2) => App(subst(t1, x, s), subst(t2, x, s))

      case Succ(t1) => Succ(subst(t1, x, s))
      case Pred(t1) => Pred(subst(t1, x, s))
      case IsZero(t1) => IsZero(subst(t1, x, s))
      case First(t1) => First(subst(t1, x, s))
      case Second(t1) => Second(subst(t1, x, s))
      case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
      case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
      //project4
      case Case(t0: Term, x1: String, t1: Term, x2: String, t2: Term) =>{
        val temp = fos.TypeBool//type would not influence reduction
        var subst1 = subst(Abs(x1, temp, t1),x,s).asInstanceOf[Abs]
        var subst2 = subst(Abs(x2, temp, t2),x,s).asInstanceOf[Abs]
        Case(subst(t0, x, s), subst1.x, subst1.y, subst2.x, subst2.y)
      }
      case Inr(t0: Term, tpe: Type) =>Inr(subst(t0, x, s),tpe)
      case Inl(t0: Term, tpe: Type) =>Inl(subst(t0, x, s),tpe)
      case Fix(t0: Term) =>{
        Fix(subst(t0, x, s))
      }

      case _ => t
    }
  }
  def IsNumbers(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t0) => IsNumbers(t0)
    case _ => false
  }
  def IsValues(t: Term): Boolean = t match {
    case True => true
    case False => true
    case Abs(v, tp, t0) => true
    case TermPair(t1, t2) => (IsValues(t1) && IsValues(t2))
    case Inl(t: Term, tpe: Type) if(IsValues(t)) => true
    case Inr(t: Term, tpe: Type) if(IsValues(t)) => true
    case _ => IsNumbers(t)
  }
  def StepToSucc(t: Term) : Term ={
    t match{
      case Succ(t1) => t1
      case _ => t
    }
  }
  def reduce(t: Term): Term = {
    t match {
      case If(True, t1: Term, t2: Term) => t1
      case If(False, t1: Term, t2: Term) => t2
      case If(cond: Term, t1: Term, t2: Term) => If(reduce(cond), t1, t2)
      case IsZero(Zero) => True
      case IsZero(Succ(t)) => {
        var tmp = t
        while(tmp.isInstanceOf[Succ]){
          tmp = StepToSucc(tmp.asInstanceOf[Succ])
        }
        if(tmp == Zero){
          False
        }else{
          IsZero(reduce(Succ(t)))
        }
      }
      case IsZero(t) => {
        IsZero(reduce(t))}
      case Pred(Zero) => Zero
      case Pred(Succ(Zero)) => Zero
      case Pred(Succ(t)) => {
        var tmp= t
        while(tmp.isInstanceOf[Succ]){
          tmp = StepToSucc(tmp.asInstanceOf[Succ])
        }
        if(tmp == Zero){
          t
        }else{
          Pred(reduce(Succ(t)))
        }
      }
      case Pred(t) => Pred(reduce(t))
      case Succ(t) => Succ(reduce(t))

      case First(t1) => t1  match{
        case TermPair(p1, p2) => IsValues(p1) && IsValues(p2) match{
          case true => p1
          case false => First(reduce(TermPair(p1, p2)))
        }
        case _ => First(reduce(t1))
      }

      case Second(t1) => t1  match{
        case TermPair(p1, p2) => IsValues(p1) && IsValues(p2) match{
          case true => p2
          case false => Second(reduce(TermPair(p1, p2)))
        }
        case _ => Second(reduce(t1))
      }

      case TermPair(p1,p2) =>IsValues(p1) match {
        case true => {
          IsValues(p2) match {
            case true => throw new NoRuleApplies(TermPair(p1, p2))
            case false => TermPair(p1, reduce(p2))
          }
        }
        case false => TermPair(reduce(p1), p2)
      }

      case App(Abs(v1, tp1, t1), Abs(v2, tp2, t2)) => {
        subst(t1, v1, Abs(v2, tp2, t2))
      }
      case App(Abs(v1, tp1, t1),t2) => IsValues(t2) match{
        case true => subst(t1, v1, t2)
        case false =>
          try {App(Abs(v1, tp1, t1),reduce(t2))}
          catch{
            case NoRuleApplies(e) => throw new NoRuleApplies(t)
          }
      }
      case App(t1,t2) =>
        try{App(reduce(t1),t2)}
        catch{
          case NoRuleApplies(e) => throw new NoRuleApplies(t)
        }

      //project 4
      case Case(t0: Term, x1: String, t1: Term, x2: String, t2: Term) =>{
        t0 match {
          //[x1 → v0] t1
          case Inl(v0: Term, tpe: Type) =>IsValues(v0) match {
            case true => subst(t1,x1,v0)
            case false =>Case(reduce(t0), x1, t1, x2, t2)
          }
          case Inr(v0: Term, tpe: Type) =>IsValues(v0) match {
            case true => subst(t2, x2, v0)
            case false => Case(reduce(t0), x1, t1, x2, t2)
          }
          case _ => Case(reduce(t0), x1, t1, x2, t2)
        }
      }
      case Inr(t0: Term, tpe: Type) =>Inr(reduce(t0),tpe)
      case Inl(t0: Term, tpe: Type) =>Inl(reduce(t0),tpe)
      case Fix(t0: Term) => t0 match{
        case Abs(x, tp, t2) => subst(t2,x, Fix(t0))
        case _=> Fix(reduce(t0))
      }
      case _ => {
        throw new NoRuleApplies(t)
      }}
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString = msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type =
    ???

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
  }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): LazyList[Term] =
    try {
      var t1 = reduce(t)
      LazyList.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        LazyList.cons(t, LazyList.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("parsed: " + trees)
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
