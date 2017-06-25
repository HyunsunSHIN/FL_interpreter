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

object Main {
  import Value._

  class EvalException(val msg: String) extends Exception


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

  def myeval(e:Expr) : Val = {
      true_eval(e,Nil,Nil)
  }

  def evaluate_args(args : List[Expr], env_ev_args : Environment_Stack) : List[EVbox] = { // call by value 라고 하자 일단
    args match {
      case Nil => Nil
      case hd::tail => { hd match {
        case EFun(params,eb) => Exprbox(hd)::evaluate_args(tail, env_ev_args)
        case _ =>  Valuebox(true_eval(hd,env_ev_args,Nil))::evaluate_args(tail,env_ev_args)
      }
        // argument 중 function 인 것은 EFun인 채로 exprbox에 넣고
        // 그 외는 모두 값을 계산해서 전달한다.
      }
    }
  }

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


  //tailrec
  def true_eval(e:Expr, env_stack_in_true_eval: Environment_Stack, arguments_in_true_eval: List[EVbox]) : Val = {
    //println("true_eval in! the expr is",e.toString)
    e match {

      case EApp(ef:Expr, eargs: List[Expr]) => {

        ef match
          {
                case EFun(params: List[String], eb: Expr) => {
                    true_eval(ef,env_stack_in_true_eval,evaluate_args(eargs,env_stack_in_true_eval))
                  }

                case EName(name) => {
                    val evaluated_args = evaluate_args(eargs,env_stack_in_true_eval)
                    true_eval(EName(name),env_stack_in_true_eval, evaluated_args)
                }
                 case _ => {

                   def last_expr_finder(x : List[Expr], formerExpr : Expr) : Expr = {
                     x match {
                       case Nil => formerExpr
                       case hd::tail => last_expr_finder(tail,hd)
                     }
                   }
                   val last_expr = last_expr_finder(eargs, ef)
                   true_eval(last_expr,env_stack_in_true_eval,Nil)
                 }
        }
      }
      case EFun(params,eb) => {
        if(params.nonEmpty && (arguments_in_true_eval == Nil)) {VFunc()}
        else {
          val params_env: Environment = env_maker_with_params_vals(params, arguments_in_true_eval)
          true_eval(eb, params_env :: env_stack_in_true_eval, Nil)
        }
      }
      case EName(x: String) => {
       // println("EName("+x+"), env_stack: " + env_stack_in_true_eval)

       @tailrec
       def stack_undwinder(env_in_stk_unwinder: Environment_Stack, x:String): (EVbox,Environment_Stack) ={
         println("env_stack_unwider in! and name we are looking for is ", x)
         env_in_stk_unwinder match {
           case Nil => println("EName error: env_stack fully consumed w/o getting name"); (Valuebox(VNil()),Nil)
           case env_stk_hd::env_stk_tail => {
             val result : Option[EVbox] = ev_finder(env_stk_hd,x)
             result match {
               case None => stack_undwinder(env_stk_tail,x)
               case Some(res) => (res,env_in_stk_unwinder)
             }
           }
         }
       }
        val stk_unwind_result = stack_undwinder(env_stack_in_true_eval,x)
        stk_unwind_result._1 match {
          case Valuebox(value) => value
          case Exprbox(expr) => true_eval(expr,stk_unwind_result._2,arguments_in_true_eval)
        }
      }

      case EHd(el:Expr) => el match {
        case ECons(eh,et) => true_eval(eh,env_stack_in_true_eval,Nil)
        case _ => println("EHd fial"); VNil()
      }

      case EConst(c) => c match {
        case CInt(n) => VInt(n)
        case CTrue() => VBool(true)
        case CFalse() => VBool(false)
        case CNil() => VNil();
        case _ => println("EConst fail"); VNil()
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
                val value_evaluated = true_eval(expr,working_environment::former_scope,Nil)
                val new_env_element : (String,EVbox) = (str,Valuebox(value_evaluated))
                val new_env = new_env_element::working_environment
                EnvMaker(tail,former_scope,new_env)
              }
            }
          }
        }

        val newly_added_scope = EnvMaker(bs,env_stack_in_true_eval,Nil)
        newly_added_scope match {
          case Nil => true_eval(eb,env_stack_in_true_eval,Nil)
          case _ => true_eval(eb, newly_added_scope::env_stack_in_true_eval,Nil)
        }
      }

      case ECons(e1, e2) => {
        val val_1 = true_eval(e1, env_stack_in_true_eval, Nil)
        val val_2 = true_eval(e2, env_stack_in_true_eval, Nil)
        println("ECons in");
        VPair(val_1, val_2)
      }

      case EEq(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1, expr2), env_stack_in_true_eval, Nil)
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
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1, expr2), env_stack_in_true_eval, Nil)
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
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1, expr2), env_stack_in_true_eval, Nil)
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

        true_eval(econd, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr) => true_eval(EIf(expr, et, ef), env_stack_in_true_eval, Nil)
          case VBool(boolean: Boolean) => boolean match {
            case true => true_eval(et, env_stack_in_true_eval, Nil)
            case false => true_eval(ef, env_stack_in_true_eval, Nil)
          }
          case _ => println("EIf failed"); VNil()
        }
      }

      case EPlus(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {

          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 + n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }
      case EMinus(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {

          case ValExpr(expr) => true_eval(EPlus(expr, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 - n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }

      case EMult(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case ValExpr(expr) => true_eval(EPlus(expr, e2), env_stack_in_true_eval, Nil)
          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case ValExpr(expr2) => true_eval(EPlus(e1, expr2), env_stack_in_true_eval, Nil)
            case VInt(n2) => VInt(n1 * n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }
      case _ => println("Other failed"); VNil()
    }
  }

  //throw new EvalException("Not implemented yet")
  def myeval_memo(e:Expr) : Val =  throw new EvalException("Not implemented yet")

}