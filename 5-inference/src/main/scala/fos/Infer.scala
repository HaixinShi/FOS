package fos

object Infer {
  case class TypeScheme(params: List[TypeVar], tp: Type)
  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  var num=0;


  case class TypeError(msg: String) extends Exception(msg)

  def fresh():TypeVar = {
    num+=1
    return TypeVar("Type"+num)
  }

  def getAbsResult(env: Env, t: Term, str: String, tmp:Type ):(Type, List[Constraint]) = {
    val (ty,con) = collect( env :+ (str,TypeScheme(Nil,tmp)), t)
    return (FunType(tmp,ty), con)
  }

  def getAppResult(env: Env, t1: Term, t2: Term, tmp:Type):(Type, List[Constraint]) = {
    val (ty1,con1) = collect(env, t1)
    val (ty2,con2) = collect(env, t2)
    return (tmp, con1 ++: con2 :+ (ty1, FunType(ty2,tmp)))
  }

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match{
    case True => (BoolType, List())
    case False => (BoolType, List())
    case Zero => (NatType, List())

    case Pred(t0) => collect(env, t0) match {
      case (tp, con) => (NatType, con :+ (tp, NatType))
    }

    case Succ(t0) => collect(env, t0) match {
      case (tp, con) => (NatType, con :+ (tp, NatType))
    }

    case IsZero(t0) => collect(env, t0) match {
      case (tp, con) =>  (BoolType, con :+ (tp, NatType))
    }

    case If(cond, t1, t2) =>
      (collect(env, t2)._1, (collect(env, cond)._1, BoolType) :: (collect(env, t1)._1, collect(env, t2)._1) :: collect(env, cond)._2 ++: collect(env, t1)._2 ++: collect(env, t2)._2)


    case Var(s) => ((env.indexWhere(_._1 == s)) != -1) match{
      case true => (env.find(_._1 == s).get._2.tp, List())
      case _ => throw new TypeError("TypeError")
    }

    case Abs(str, tp, t) => tp match{
      case EmptyTypeTree() => getAbsResult(env, t, str, fresh())
      case _=> getAbsResult(env, t, str, tp.tpe)
    }

    case App(t1,t2) => getAppResult(env, t1, t2, fresh())

    case _ => throw new TypeError("TypeError")
  }
  //def isVariable
  //check if s appears in t
  def isAppear(s:Type, t:Type): Boolean ={
    s == t match {
      case true => true
      case false =>{
        t match{
          case FunType(t1: Type, t2: Type) => isAppear(s,t1) || isAppear(s, t2)
          case _ => false
        }
      }
    }
  }
  def unify(c: List[Constraint]): Type => Type = {
    c.isEmpty match{
      case true =>ty => ty
      case false => {
        val (s,t) = c.head
        s.getClass == t.getClass match {
          case true => unify(c.tail)
          case false =>{
            (s.isInstanceOf[TypeVar],t.isInstanceOf[TypeVar]) match {
              case (true, true) => unify(c.tail)
              case (true, false) =>{
                isAppear(s,t) match{
                  case true => throw new TypeError("TypeError")
                  case false => {
                    //TODO:extend substitution
                    //TODO:apply this substitution to c.tail
                    //Map()
                    unify(c.tail.map{x => (substitution(x._1, s, t),substitution(x._2, s, t))}).compose { ty => substitution(ty, s, t)}
                  }
                }
              }
              case (false, true) =>{
                //TODO:the same as before
                //Map()
                unify(c.tail.map{x => (substitution(x._1, t, s),substitution(x._2, t, s))}).compose { ty => substitution(ty, t, s)}
              }
              case (false, false) =>{
                (s,t) match {
                  case (FunType(s1: Type, s2: Type),FunType(t1: Type, t2: Type)) =>{
                    //TODO:recursively unify S1 and T1 as well as S2 and T2, and proceed to the next constraint.
                    //Map()
                    unify((s2,t2)::(s1,t1)::c.tail)
                  }
                  case _ => throw new TypeError("TypeError")
                }
              }
            }
          }
        }
      }
    }
  }
  //[x->t]s
  def substitution(s:Type, x:Type, t:Type):Type = {
    s match{
      case FunType(s1: Type, s2: Type) => FunType(substitution(s1,x,t),substitution(s2,x,t))
      case _=>{
        s == x match{
          case true => t
          case false => s
        }
      }
    }
  }
}
