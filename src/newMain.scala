package pp201701.proj
import scala.annotation.tailrec
import pp201701.proj.Data.DataBundle._
import scala.collection.immutable._

object Value {
  type Environment_Stack = List[Environment]
  type Environment = List[(String,EVbox)]

  sealed abstract class EVbox
  case class Exprbox(e: Expr) extends  EVbox
  case class Valuebox(v: Val) extends EVbox

  sealed abstract class Val
  case class ValExpr(expr: Expr) extends Val
  case class VNil() extends Val
  case class VInt(n: Int) extends Val
  case class VBool(boolean: Boolean) extends Val
  case class VPair(epxr1: Val, expr2: Val) extends Val
  case class VFunc() extends Val

  abstract class ConvertToScala[A] {
    def toInt(a:A) : Option[Int]
    def toBool(a:A) : Option[Boolean]
    def toPair(a:A) : Option[(A, A)]
    def isNil(a:A) : Boolean
    def isFun(a:A) : Boolean
  }

  implicit val valConv : ConvertToScala[Val] = new ConvertToScala[Val] {

    override def toInt(a: Val): Option[Int] = a match {
      case VInt(n : Int) => Some(n)
      case _ => None
    }

    override def isNil(a: Val): Boolean =  a match {
      case VNil() => true
      case _ => false
    }
    override def toPair(a: Val): Option[(Val, Val)] = a match {
      case VPair(val1,val2) => Some(val1, val2)
      case _ => None
    }

    override def toBool(a: Val): Option[Boolean] = a match {
      case VBool(bool) => Some(bool)
      case _ => None
    }

    override def isFun(a: Val): Boolean = true//a match {}
  }
}

class newMain {

  import Value._

  val myhash = collection.mutable.HashMap.empty[(Expr,List[EVbox]),Val]

  def true_eval_memo(e:Expr, env_stack_in_true_eval: Environment_Stack, arguments_in_true_eval: List[EVbox]) : Val = {
    println("true_eval in! the expr is",e.toString)

    def env_maker_with_params_vals(param_input: List[String], args_input: List[EVbox])
    : Environment = param_input match {
      case Nil => Nil
      case hd_params::tail_params => args_input match {
        case hd_args::tail_args => {
          val params_arg_element = (hd_params, hd_args)
          params_arg_element::env_maker_with_params_vals(tail_params,tail_args)
        }
        // 기본적으로 call by value로 호출이었으나 hd_args가 function 인 경우에만 한해서
        // Expr으로 전달된다.
        case Nil => Nil //println("EApp Error! :IN PARAMS VALS");
        // This line can be excecuted when construction of fucntion
        // without giving any argument to it.
      }
    }

    e match {

      case EApp(ef:Expr, eargs: List[Expr]) => {

        myhash.get((ef,evaluate_args(eargs))) match {
          case None => {
            ef match
            {
              case EFun(params: List[String], eb: Expr) => {
                val result = true_eval_memo(ef,env_stack_in_true_eval,evaluate_args(eargs))
                myhash.update((ef,evaluate_args(eargs)),result)
                result
              }

              case EName(name) => {
                val evaluated_args = evaluate_args(eargs)
                val result = true_eval_memo(EName(name),env_stack_in_true_eval, evaluated_args)
                myhash.update((ef,evaluate_args(eargs)),result)
                result
              }

              case _ => {
                def excecute_list_of_expr(x : List[Expr], formerVal : Val) : Val = {
                  x match {
                    case Nil => formerVal
                    case hd::tail =>  excecute_list_of_expr(tail,true_eval_memo(hd,env_stack_in_true_eval,Nil))
                  }
                }
                val intermediate_result = true_eval_memo(ef,env_stack_in_true_eval,Nil)
                excecute_list_of_expr(eargs,intermediate_result)
              }
            }
          }
          case Some(value) => value

        }

        def evaluate_args(args : List[Expr]) : List[EVbox] = { // call by value 라고 하자 일단
          args match {
            case Nil => Nil
            case hd::tail => { hd match {
              case EFun(params,eb) => Exprbox(hd)::evaluate_args(tail)
              case _ =>  Valuebox(true_eval_memo(hd,env_stack_in_true_eval,Nil))::evaluate_args(tail)
            }
              // argument 중 function 인 것은 EFun인 채로 exprbox에 넣고
              // 그 외는 모두 값을 계산해서 전달한다.
            }
          }
        }
        // 새롭게 arg_environment를 만든다고 생각하면 된다. 그리고 기본적인 env Stack 과 독립적으로 줄 것 임
      }
      case EFun(params,eb) => {
        if(params.nonEmpty && (arguments_in_true_eval == Nil)) {VFunc()}
        else {
          val params_env: Environment = env_maker_with_params_vals(params, arguments_in_true_eval)
          true_eval_memo(eb, params_env :: env_stack_in_true_eval, Nil)
        }
      }

      case ELet(bs:List[Bind], eb:Expr) => {
        println("Elet in!")
        def EnvMaker(bs: List[Bind], former_scope:Environment_Stack, working_environment :Environment)
        : Environment = {

          bs match {
            case Nil => working_environment
            case (bkind,str,expr):: tail => bkind match {
              case BDEF() => {
                val new_env_element : (String,EVbox) = (str,Exprbox(expr))
                val new_working_env = new_env_element::working_environment
                EnvMaker(tail,former_scope,new_working_env)
              }
              case BVAL() => {
                val value_evaluated = true_eval_memo(expr,working_environment::former_scope,Nil)
                val new_env_element : (String,EVbox) = (str,Valuebox(value_evaluated))
                val new_env = new_env_element::working_environment
                EnvMaker(tail,former_scope,new_env)
              }
            }
          }
        }

        val newly_added_scope = EnvMaker(bs,env_stack_in_true_eval,Nil)
        newly_added_scope match {
          case Nil => true_eval_memo(eb,env_stack_in_true_eval,Nil)
          case _ => true_eval_memo(eb, newly_added_scope::env_stack_in_true_eval,Nil)
        }
      }

      case EName(x: String) => {

        println("EName("+x+"), env_stack: " + env_stack_in_true_eval)

        @tailrec
        def ev_finder(env_in_ev_finder: Environment, x:String) : Option[EVbox] = {
          println("env_in_ev_finder: ",env_in_ev_finder)
          env_in_ev_finder match {
            case Nil => None
            case hd::tail => {
              if ( hd._1 == x ) { /*print("got you!");*/ Some(hd._2) }
              else ev_finder(tail,x)
            }
          }
        }

        @tailrec
        def stack_undwinder(env_in_stk_unwinder: Environment_Stack, x:String): Val ={
          println("env_stack_unwider in! and name we are looking for is ", x)
          env_in_stk_unwinder match {
            case Nil => println("EName error: env_stack fully consumed w/o getting name"); VNil();
            case env_stk_hd::env_stk_tail => {
              val result : Option[EVbox] = ev_finder(env_stk_hd,x)
              result match {
                case None => stack_undwinder(env_stk_tail,x)
                case Some(res) =>  res match {
                  case Exprbox(expr) => {
                    true_eval_memo(expr,env_in_stk_unwinder,arguments_in_true_eval)
                    // The reason why argument_list, just List[val] is transmitted to the Efun,
                    // not the Environment(List[(String,Val)]),
                    // is because we don't know the params at this point.
                    // So, We deliver just argument_list which is received to the EName()
                    // (This was transferred at EApp() with true_eval(EName(),env,arguments)
                  }
                  case Valuebox(value) => value
                }
              }
            }
          }
        }
        stack_undwinder(env_stack_in_true_eval,x)
      }

      case EHd(el:Expr) => el match {
        case ECons(eh,et) => true_eval_memo(eh,env_stack_in_true_eval,Nil)
        case _ => println("EHd fial"); VNil()
      }

      case EConst(c) => c match {
        case CInt(n) => VInt(n)
        case CTrue() => VBool(true)
        case CFalse() => VBool(false)
        case CNil() => VNil();
        case _ => println("EConst fail"); VNil()
      }

      case ECons(e1, e2) => {
        val val_1 = true_eval_memo(e1, env_stack_in_true_eval, Nil)
        val val_2 = true_eval_memo(e2, env_stack_in_true_eval, Nil)
        println("ECons in");
        VPair(val_1, val_2)
      }

      case EEq(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval_memo(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval_memo(EEq(e1, expr2), env_stack_in_true_eval, Nil)
              case VInt(n2) => {
                if (n1 == n2) VBool(true) else VBool(false)
              }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("EEQ failed"); VNil()
        }
      }

      case ELt(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval_memo(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval_memo(EEq(e1, expr2), env_stack_in_true_eval, Nil)
              case VInt(n2) => {
                if (n1 > n2) VBool(true) else VBool(false)
              }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("ELT failed"); VNil()
        }
      }

      case EGt(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval_memo(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval_memo(EEq(e1, expr2), env_stack_in_true_eval, Nil)
              case VInt(n2) => {
                if (n1 > n2) VBool(true) else VBool(false)
              }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("ELT failed"); VNil()
        }
      }

      case EIf(econd: Expr, et: Expr, ef: Expr) => {
        true_eval_memo(econd, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr) => true_eval_memo(EIf(expr, et, ef), env_stack_in_true_eval, Nil)
          case VBool(boolean: Boolean) => boolean match {
            case true => true_eval_memo(et, env_stack_in_true_eval, Nil)
            case false => true_eval_memo(ef, env_stack_in_true_eval, Nil)
          }
          case _ => println("EIf failed"); VNil()
        }
      }

      case EPlus(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

          case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval_memo(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 + n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }
      case EMinus(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

          case ValExpr(expr) => true_eval_memo(EPlus(expr, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval_memo(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 - n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }

      case EMult(e1, e2) => {
        true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

          case ValExpr(expr) => true_eval_memo(EPlus(expr, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval_memo(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 * n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }
      case _ => println("Other failed"); VNil()
    }
  }
}