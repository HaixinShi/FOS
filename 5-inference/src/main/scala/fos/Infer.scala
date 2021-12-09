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

  def getAbsResult(env: Env, t: Term, str: String, tmp:TypeVar ):(Type, Constraint) = {
    val (ty,con) = collect((str,TypeScheme(Nil,tmp)) ++ env,t)
    return (FunType(tmp,ty), con)
  }

  def getAppResult(env: Env, t1: Term, t2: Term, tmp:TypeVar):(Type, Constraint) = {
    val (ty1,con1) = collect(env, t1)
    val (ty2,con2) = collect(env, t2)
    return (tmp, con1 ++ con2 ++ List((ty1, FunType(ty2,type1))))
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
      (collect(env, t2)._1, collect(env, cond)._2 ++ collect(env, t1)._2 ++ collect(env, t2)._2 ++ List((collect(env, cond)._1, BoolType),(collect(env, t1)._1,collect(env, t2)._1))  )
          

    case Var(s) => ((env.indexWhere(_._1 == s)) != -1) match{
      case true => (env.find(_._1 == s).get._2.tp, List()) 
      case _ => throw new TypeError("TypeError")
    }

    case Abs(str, tp, t) => tp match{
      case EmptyTypeTree => getAbsResult(env, t, str, fresh())
      case _=> getAbsResult(env, t, str, tp.tpe)
    }

    case App(t1,t2) => getAppResult(env, t1, t2, fresh())
  
    case _ => throw new TypeError("TypeError")
  }





  def unify(c: List[Constraint]): Type => Type = ???
}
