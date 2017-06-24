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


  def env_maker_with_params_vals(param_input: List[String], args_input: List[Val])
  : Environment = param_input match {
    case Nil => Nil
    case hd_params::tail_params => args_input match {
      case hd_args::tail_args => {
        val params_arg_element = ( hd_params,Valuebox(hd_args) )
        params_arg_element::env_maker_with_params_vals(tail_params,tail_args)
      }  // 기본적으로 call by value로 호출
      case Nil => println("EApp Error! :IN PARAMS VALS"); Nil
    }
  }

  def myeval(e:Expr) : Val = {
      true_eval(e,Nil,Nil)
  }

  def true_eval(e:Expr, env_stack_in_true_eval: Environment_Stack, arguments_in_true_eval: List[Val]) : Val = {
    println("true_eval in! the expr is",e.toString)
    e match {

      case EApp(ef:Expr, eargs: List[Expr]) => {
        ef match {
        case EFun(params: List[String], eb: Expr) => {
           def evaluate_args(args : List[Expr]) : List[Val] = { // call by value 라고 하자 일단
              args match {
                case Nil => Nil
                case hd::tail => true_eval(hd,env_stack_in_true_eval,Nil)::evaluate_args(tail)
              }
            }
            true_eval(ef,env_stack_in_true_eval,evaluate_args(eargs))
          }

          case EName(name) => {

            def evaluate_args(args : List[Expr]) : List[Val] = { // call by value 라고 하자 일단
                    args match {
                      case Nil => Nil
                      case hd::tail => true_eval(hd,env_stack_in_true_eval,Nil)::evaluate_args(tail)
                    }
              }
              val evaluated_args = evaluate_args(eargs)
              true_eval(EName(name),env_stack_in_true_eval, evaluated_args)
          }
           case _ => {
             def excecute_list_of_expr(x : List[Expr], formerVal : Val) : Val = {
               x match {
                 case Nil => formerVal
                 case hd::tail =>  excecute_list_of_expr(tail,true_eval(hd,env_stack_in_true_eval,Nil))
               }
             }
             val intermediate_result = true_eval(ef,env_stack_in_true_eval,Nil)
             excecute_list_of_expr(eargs,intermediate_result)
             // 1) 괄호가 중첩된 경우를 manage. - args = Nil인 경우가 됨
             // 2) 여러개의 Expression 이 sequential 하게 들어오는 경우
             //    마지막 것만을 출력해줄 수 있도록 함
             //    ex> ( (+ 1 3) (- 1 2) 3 )
             //     => 3 출력
             //    ex> ((3))
             //     => 3 출력
           }
        }
        // 새롭게 arg_environment를 만든다고 생각하면 된다. 그리고 기본적인 env Stack 과 독립적으로 줄 것 임
      }

      case EFun(params,eb) => {
        val params_env : Environment = env_maker_with_params_vals(params,arguments_in_true_eval)
        true_eval(eb,params_env::env_stack_in_true_eval, Nil)
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

      case EName(x: String) => {

        println("EName("+x+"), env_stack: " + env_stack_in_true_eval)

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
                     true_eval(expr,env_in_stk_unwinder,arguments_in_true_eval)
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

      case ECons(e1,e2) => {
        val val_1 = true_eval(e1,env_stack_in_true_eval,Nil)
        val val_2 = true_eval(e2,env_stack_in_true_eval,Nil)
        println("ECons in"); VPair(val_1,val_2)
      }

      case EEq(e1,e2) => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => {
            true_eval(e2,env_stack_in_true_eval,Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1,expr2),env_stack_in_true_eval,Nil)
              case VInt(n2) => { if(n1 == n2) VBool(true) else VBool(false) }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("EEQ failed"); VNil()
        }
      }

      case ELt(e1,e2) => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => {
            true_eval(e2,env_stack_in_true_eval,Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1,expr2),env_stack_in_true_eval,Nil)
              case VInt(n2) => { if(n1 > n2) VBool(true) else VBool(false) }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("ELT failed"); VNil()
        }
      }

      case EGt(e1,e2) => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {
          case ValExpr(expr1) => true_eval(EEq(expr1,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => {
            true_eval(e2,env_stack_in_true_eval,Nil) match {
              case ValExpr(expr2) => true_eval(EEq(e1,expr2),env_stack_in_true_eval,Nil)
              case VInt(n2) => { if(n1 > n2) VBool(true) else VBool(false) }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("ELT failed"); VNil()
        }
      }


      case EIf(econd:Expr, et:Expr, ef:Expr) => {
        true_eval(econd,env_stack_in_true_eval,Nil) match {
          case ValExpr(expr) => true_eval( EIf(expr,et,ef), env_stack_in_true_eval,Nil)
          case VBool(boolean: Boolean) => boolean match {
            case true => true_eval(et,env_stack_in_true_eval,Nil)
            case false => true_eval(ef,env_stack_in_true_eval,Nil)
          }
          case _ => println("EIf failed"); VNil()
        }
      }

      case EPlus(e1, e2)  => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {

          case ValExpr(expr) => true_eval( EPlus(expr,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => true_eval(e2,env_stack_in_true_eval,Nil) match {
            case ValExpr(expr2) => true_eval( EPlus(e1,expr2),env_stack_in_true_eval,Nil)
            case VInt(n2) => VInt(n1+n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }

      case EMinus(e1, e2)  => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {

          case ValExpr(expr) => true_eval( EPlus(expr,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => true_eval(e2,env_stack_in_true_eval,Nil) match {
            case ValExpr(expr2) => true_eval( EPlus(e1,expr2),env_stack_in_true_eval,Nil)
            case VInt(n2) => VInt(n1-n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }

      case EMult(e1, e2)  => {
        true_eval(e1,env_stack_in_true_eval,Nil) match {

          case ValExpr(expr) => true_eval( EPlus(expr,e2),env_stack_in_true_eval,Nil)
          case VInt(n1) => true_eval(e2,env_stack_in_true_eval,Nil) match {
            case ValExpr(expr2) => true_eval( EPlus(e1,expr2),env_stack_in_true_eval,Nil)
            case VInt(n2) => VInt(n1*n2)
            case _ => println("EPlus failed"); VNil()
          }
          case _ => println("EPlus failed"); VNil()
        }
      }


      case _ =>  println("Other failed"); VNil()


    }
  }

  //throw new EvalException("Not implemented yet")
  def myeval_memo(e:Expr) : Val = throw new EvalException("Not implemented yet")

}