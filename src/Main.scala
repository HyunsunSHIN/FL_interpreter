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
    case class VPair() extends Val
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
     override def isNil(a: Val): Boolean = true //a match { case}
     override def toPair(a: Val): Option[(Val, Val)] = Some((VNil(),VNil()))//a match {}
     override def toBool(a: Val): Option[Boolean] = None//a match {}
     override def isFun(a: Val): Boolean = true//a match {}
   }
}

object Main {
  import Value._

  class EvalException(val msg: String) extends Exception


  def env_maker_with_params(param_input: List[String], args_input: List[Expr], environment_stack: Environment_Stack)
  : Environment = param_input match {
    case Nil => Nil
    case hd_params::tail_params => args_input match {
      case hd_args::tail_args => {
        val params_arg_element = (hd_params,Valuebox(true_eval(hd_args,environment_stack)))
        params_arg_element::env_maker_with_params(tail_params,tail_args, environment_stack)
      }  // 기본적으로 call by value로 호출
      case Nil => println("EApp Error!"); Nil
    }
  }

  def myeval(e:Expr) : Val = {
      true_eval(e,Nil)
  }

  def true_eval(e:Expr, environment_stack: Environment_Stack) : Val = {
    println("true_eval in! the expr is",e.toString)
    e match {

      case EApp(ef:Expr, eargs: List[Expr]) => {

        ef match {
          case EFun(params: List[String], eb: Expr) => {
            val env_in_func = env_maker_with_params(params,eargs,environment_stack)
            true_eval(ef,env_in_func::environment_stack)
          }

          case EName(name) => {

              def evaluate_args(args : List[Expr]) : List[Val] = { // call by value 라고 하자 일단
                    args match {
                      case Nil => Nil
                      case hd::tail => true_eval(hd,environment_stack)::evaluate_args(tail)
                    }
              }
              // true_eval(EName())

          }

          case _ => println("EApp Error"); VNil()
        }
        // 새롭게 arg_environment를 만든다고 생각하면 된다. 그리고 기본적인 env Stack 과 독립적으로 줄 것 임

      }

      case EFun(params,eb) => { true_eval(eb,environment_stack) }

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
                val value_evaluated = true_eval(expr,working_environment::former_scope)
                val new_env_element : (String,EVbox) = (str,Valuebox(value_evaluated))
                val new_env = new_env_element::working_environment
                EnvMaker(tail,former_scope,new_env)
              }
            }
          }
        }

        val newly_added_scope = EnvMaker(bs,environment_stack,Nil)
        newly_added_scope match {
          case Nil => true_eval(eb,environment_stack)
          case _ => true_eval(eb, newly_added_scope::environment_stack)
        }
      }

      case EName(x: String) => {

        println("EName("+x+"), env_stack: " + environment_stack)

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

                   case Exprbox(expr) => true_eval(expr,env_in_stk_unwinder)
                   case Valuebox(value) => value
                 }
               }
             }
           }
        }

        stack_undwinder(environment_stack,x)
      }

      case EHd(el:Expr) => el match {
        case ECons(eh,et) => true_eval(eh,environment_stack)
        case _ => println("EHd fial"); VNil()
      }

      case EConst(c) => c match {
        case CInt(n) => VInt(n)
        case CTrue() => VBool(true)
        case CFalse() => VBool(false)
        case _ => println("EConst fial"); VNil()
      }

      //same version ELq, EGq must be made.

      case EEq(e1,e2) => {
        true_eval(e1,environment_stack) match {
          case ValExpr(expr1) => true_eval(EEq(expr1,e2),environment_stack)
          case VInt(n1) => {
            true_eval(e2,environment_stack) match {
              case ValExpr(expr2) => true_eval(EEq(e1,expr2),environment_stack)
              case VInt(n2) => { if(n1 == n2) VBool(true) else VBool(false) }
              case _ => println("VInt failed"); VNil()
            }
          }
          case _ => println("EEQ failed"); VNil()
        }
      }

      case EIf(econd:Expr, et:Expr, ef:Expr) => {
        true_eval(econd,environment_stack) match {
          case ValExpr(expr) => true_eval( EIf(expr,et,ef), environment_stack)
          case VBool(boolean: Boolean) => boolean match {
            case true => true_eval(et,environment_stack)
            case false => true_eval(ef,environment_stack)
          }
          case _ => println("EIf failed"); VNil()
        }
      }

      //same version EMult, EMinus must be made.
      case EPlus(e1, e2)  => {
        true_eval(e1,environment_stack) match {

          case ValExpr(expr) => true_eval( EPlus(expr,e2),environment_stack)
          case VInt(n1) => true_eval(e2,environment_stack) match {
            case ValExpr(expr2) => true_eval( EPlus(e1,expr2),environment_stack )
            case VInt(n2) => VInt(n1+n2)
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