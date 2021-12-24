package fos
import scala.collection.mutable.ListBuffer

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
    val (ty,con) = collect((str,TypeScheme(List(),tmp))::env, t)
    return (FunType(tmp,ty), con)
  }

  def getAppResult(env: Env, t1: Term, t2: Term, tmp:Type):(Type, List[Constraint]) = {
    val (ty1,con1) = collect(env, t1)
    val (ty2,con2) = collect(env, t2)
    return (tmp, con1 ++: con2 :+ (ty1, FunType(ty2,tmp)))
  }

  def getLetResult(env: Env, str: String, v: Term, t: Term): (Type, List[Constraint]) = {
    val (type_v, con_v) = collect(env, v)     // type the v obtaining a type S and a set of constraints C
    val s_to_t = unify(con_v)         // use unification on C
    val new_t = s_to_t(type_v)        // find the new type T for S
    var new_env = env.map(pair => (pair._1, TypeScheme(pair._2.params, s_to_t(pair._2.tp)))) // apply the substitution to the current env
    //generalize some type variables inside T and obtain a type scheme.
    val gen_T = ((getTypeVar(new_t).filterNot(tv => new_env.exists(e => isAppear(e._2.tp, tv))))).distinct   // get the remaining typeVar in T
    val x_tpsch = TypeScheme(gen_T, new_t)
    new_env = new_env :+ (str, x_tpsch)
    return collect(new_env, t)
  }

  def getTypeVar(tp: Type): List[TypeVar] = tp match {
    case y@TypeVar(name) =>  List(y)                // generate fresh type variables
    case FunType(t1, t2) => (getTypeVar(t1) ++ getTypeVar(t2))
    case _ => Nil
  }

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match{
    case True => (BoolType, List())
    case False => (BoolType, List())
    case Zero => (NatType, List())

    case Pred(t0) => collect(env, t0) match {
      case (tp, con) => (NatType, (tp, NatType) +: con)
    }

    case Succ(t0) => collect(env, t0) match {
      case (tp, con) => (NatType, (tp, NatType) +: con)
    }

    case IsZero(t0) => collect(env, t0) match {
      case (tp, con) =>  (BoolType, (tp, NatType) +: con)
    }

    case If(cond, t1, t2) =>
      (collect(env, t2)._1, (collect(env, cond)._1, BoolType) :: (collect(env, t1)._1, collect(env, t2)._1) :: collect(env, cond)._2 ++: collect(env, t1)._2 ++: collect(env, t2)._2)


    case Var(s) => ((env.indexWhere(_._1 == s)) != -1) match{
      case true =>
        val s_tpscheme = env.find(_._1 == s).get._2
        val already_exist = (s_tpscheme.params.exists((p) => getTypeVar(s_tpscheme.tp).exists((t) => t == p)))
        if (already_exist) {
          (fresh(), List())
        } else {
          (s_tpscheme.tp, List())
        }
      case _ => throw new TypeError("TypeError")
    }

    case Abs(str, tp, t) => tp match{
      case EmptyTypeTree() => getAbsResult(env, t, str, fresh())
      case _ => getAbsResult(env, t, str, tp.tpe)
    }

    case App(t1,t2) => getAppResult(env, t1, t2, fresh())

    case Let(x, tp, v, t) =>
      val (type_v, con_v) = collect(env, v)
      val (type_t, con_t) = getLetResult(env, x, v, t)
      tp match{
//        case EmptyTypeTree() => (type_t, (con_v ++ con_t))
//        case _=> (type_t, (con_v ++ ((type_v, tp.tpe) +: con_t)))
        case EmptyTypeTree() => (type_t, con_t)
        case _ => collect(env, App(Abs(x, tp, t), v))
    }

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
      case true => ty => ty
      case false => {
        val (s,t) = c.head
        s == t match {
          case true => unify(c.tail)
          case false =>{
            (s.isInstanceOf[TypeVar],t.isInstanceOf[TypeVar]) match {
              case (true, _) =>{
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
              case (_, true) =>{
                //TODO:the same as before
                //Map()
                isAppear(t,s) match{
                  case true => throw new TypeError("TypeError")
                  case false => {
                    unify(c.tail.map{x => (substitution(x._1, t, s),substitution(x._2, t, s))}).compose { ty => substitution(ty, t, s)}
                  }
                }
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
              case _ =>throw new TypeError("TypeError")
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
