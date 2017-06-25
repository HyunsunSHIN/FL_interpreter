package pp201701.proj

import scala.annotation.tailrec
import pp201701.proj.Data.DataBundle._
import scala.collection.immutable._

object Value {

  type Environment_Stack = List[Environment]
  type Environment = List[(String, EVbox)]

  sealed abstract class EVbox

  case class Exprbox(e: Expr) extends EVbox

  case class Valuebox(v: Val) extends EVbox

  sealed abstract class Val

  case class ValExpr(expr: Expr) extends Val

  case class VNil() extends Val

  case class VInt(n: Int) extends Val

  case class VBool(boolean: Boolean) extends Val

  case class VPair(epxr1: Val, expr2: Val) extends Val

  case class VFunc() extends Val

  abstract class ConvertToScala[A] {
    def toInt(a: A): Option[Int]

    def toBool(a: A): Option[Boolean]

    def toPair(a: A): Option[(A, A)]

    def isNil(a: A): Boolean

    def isFun(a: A): Boolean
  }

  implicit val valConv: ConvertToScala[Val] = new ConvertToScala[Val] {

    override def toInt(a: Val): Option[Int] = a match {
      case VInt(n: Int) => Some(n)
      case _ => None
    }

    override def isNil(a: Val): Boolean = a match {
      case VNil() => true
      case _ => false
    }

    override def toPair(a: Val): Option[(Val, Val)] = a match {
      case VPair(val1, val2) => Some(val1, val2)
      case _ => None
    }

    override def toBool(a: Val): Option[Boolean] = a match {
      case VBool(bool) => Some(bool)
      case _ => None
    }

    override def isFun(a: Val): Boolean = true //a match {}
  }
}

object Main {

  import Value._

  class EvalException(val msg: String) extends Exception

  def myeval(e: Expr): Val = {
    true_eval(e, Nil, Nil)
  }

  // parameter들과 argument를 받아서 Environment를 생성하는 함수
  def env_maker_with_params_vals(param_input: List[String], args_input: List[EVbox])
  : Environment = param_input match {

    case Nil => Nil
    case hd_params :: tail_params => args_input match {
      case hd_args :: tail_args => {
        val params_arg_element = (hd_params, hd_args)
        params_arg_element :: env_maker_with_params_vals(tail_params, tail_args)
      }

      // 기본적으로 call by value로 호출이었으나 hd_args가 function 인 경우에만 한해서
      // Expr으로 전달되므로 List[EVBox]를 반환한다.

      case Nil => Nil
      // This line will be reached only when construction of function
      // without giving any argument to it.
    }
  }

  // Function 에서 전달할 argument List(: List[Expr])에 대하여,
  // EFUNC 인 경우는 EVBox에 Expr으로 넣고 그 외는 evaluate 해서 새로운 List[EVbox]를 만들어 반환하는 함수

  def evaluate_args(args: List[Expr], env_ev_args: Environment_Stack): List[EVbox] = {
    args match {
      case Nil => Nil
      case hd :: tail => {
        hd match {
          case EFun(params, eb) => Exprbox(hd) :: evaluate_args(tail, env_ev_args)
          case _ => Valuebox(true_eval(hd, env_ev_args, Nil)) :: evaluate_args(tail, env_ev_args)
        }
      }
    }
  }


  // Environment 에서 해당 name에 대응되는 EVBox가 있는지에 대한 Option[EVBox] 를 반환하는 함수
  @tailrec
  def ev_finder(env_in_ev_finder: Environment, x: String): Option[EVbox] = {

    env_in_ev_finder match {
      case Nil => None
      case hd :: tail => {
        if (hd._1 == x) {
          Some(hd._2)
        }
        else ev_finder(tail, x)
      }
    }
  }


  // 어떤 Expression을 받아서, 현재 environment Stack 정보(name과 EVBox list의 list)를 활용하여
  // Value 를 return 하는 함수. 비록 tailrec 은 아니지만
  // tail rec input에 대해서는 tailrec 처럼 행동한다.

  def true_eval(e: Expr, env_stack_in_true_eval: Environment_Stack, arguments_in_true_eval: List[EVbox]): Val = {
    e match {

      case EApp(ef: Expr, eargs: List[Expr]) => {

        ef match {
          case EFun(params: List[String], eb: Expr) => {
            true_eval(ef, env_stack_in_true_eval, evaluate_args(eargs, env_stack_in_true_eval))
          }
          case EName(name) => {
            val evaluated_args = evaluate_args(eargs, env_stack_in_true_eval)
            true_eval(EName(name), env_stack_in_true_eval, evaluated_args)
          }
          case _ => {
            // 사실은 이 곳에 들어오면 안된다.
            // 왜냐하면 EApp은 Function Application 에만 해당하기 때문이다.
            // 그러므로 function name이거나 EFun이거나 둘 중 하나여야 한다
            // 하지만 그럼에도 불구하고 이곳에 들어왔다면 즉 (E1 E2 ...  En) 형태라면,
            // 마지막 En 만 실행하도록 한다.

            def last_expr_finder(x: List[Expr], formerExpr: Expr): Expr = {
              x match {
                case Nil => formerExpr
                case hd :: tail => last_expr_finder(tail, hd)
              }
            }
            val last_expr = last_expr_finder(eargs, ef)
            true_eval(last_expr, env_stack_in_true_eval, Nil)
          }
        }
      }
      case EFun(params, eb) => {

        // 파라미터가 0도 아닌데, argument를 전달 받지 못했다는 것은 function 이
        // 반환되며 불려진 경우다.
        // EFun 이 사용되는 곳은 크게
        // 1) EApp 에서 - argument 전달
        // 2) def x EFun - 이 때 정의만 하기 때문에 evaluate 하지 않음. 고로 여기에 도달할 수 없음
        // 3) EFun 을 반환 할 때 - argument도 없다.
        // 따라서 parameter의 수가 0 개가 아닌데 argument가 전달되지 않았다면,
        // 함수를 반환하는 경우가 될 것 이다.

        if (params.nonEmpty && (arguments_in_true_eval == Nil)) {
          VFunc()
        }

        else {
        // 그게 아니라면 전달 받은 argument와 parameter를 결합하여 새로운 Environemnt를 만들고
        // 그 환경하에서 function body를 evaluate 한다.
          val params_env: Environment = env_maker_with_params_vals(params, arguments_in_true_eval)
          true_eval(eb, params_env :: env_stack_in_true_eval, Nil)
        }
      }

      // name을 만났을 때 Value를 return하는 함수이다.
      case EName(x: String) => {

        @tailrec
        def stack_undwinder(env_in_stk_unwinder: Environment_Stack, x: String): (EVbox, Environment_Stack) = {
          env_in_stk_unwinder match {
            case Nil => (Valuebox(VNil()), Nil) //EName error: env_stack fully consumed w/o getting name
            case env_stk_hd :: env_stk_tail => {
              val result: Option[EVbox] = ev_finder(env_stk_hd, x)
              result match {
                case None => stack_undwinder(env_stk_tail, x)
                case Some(res) => (res, env_in_stk_unwinder)
              }
            }
          }
        }
        val stk_unwind_result = stack_undwinder(env_stack_in_true_eval, x)
        stk_unwind_result._1 match {
          case Valuebox(value) => value
          case Exprbox(expr) => true_eval(expr, stk_unwind_result._2, arguments_in_true_eval)
        }
      }

      case EHd(el: Expr) => el match {
        case ECons(eh, et) => true_eval(eh, env_stack_in_true_eval, Nil)
        case _ => VNil() //println("EHd fial");
      }

      case ETl(el: Expr) => el match {
        case ECons(eh, et) => true_eval(et, env_stack_in_true_eval, Nil)
        case _ => VNil() //println("EHd fial");
      }

      case EConst(c) => c match {
        case CInt(n) => VInt(n)
        case CTrue() => VBool(true)
        case CFalse() => VBool(false)
        case CNil() => VNil();
        case _ => VNil() //println("EConst fail");
      }

      case ELet(bs: List[Bind], eb: Expr) => {

        def EnvMaker(bs: List[Bind], former_scope: Environment_Stack, working_environment: Environment)
        : Environment = {

          bs match {
            case Nil => working_environment
            case (bkind, str, expr) :: tail => bkind match {
              case BDEF() => {
                val new_env_element: (String, EVbox) = (str, Exprbox(expr))
                val new_working_env = new_env_element :: working_environment
                EnvMaker(tail, former_scope, new_working_env)
              }
              case BVAL() => {
                val value_evaluated = true_eval(expr, working_environment :: former_scope, Nil)
                val new_env_element: (String, EVbox) = (str, Valuebox(value_evaluated))
                val new_env = new_env_element :: working_environment
                EnvMaker(tail, former_scope, new_env)
              }
            }
          }
        }

        val newly_added_scope = EnvMaker(bs, env_stack_in_true_eval, Nil)

        newly_added_scope match {
          case Nil => true_eval(eb, env_stack_in_true_eval, Nil)
          case _ => true_eval(eb, newly_added_scope :: env_stack_in_true_eval, Nil)
        }
      }

      case ECons(e1, e2) => {
        val val_1 = true_eval(e1, env_stack_in_true_eval, Nil)
        val val_2 = true_eval(e2, env_stack_in_true_eval, Nil)
        VPair(val_1, val_2)
      }

      case EEq(e1, e2) => {

        true_eval(e1, env_stack_in_true_eval, Nil) match {

          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => {
                if (n1 == n2) VBool(true) else VBool(false)
              }
              case _ => VNil() //VInt failed
            }
          }
          case _ =>  VNil() // EEQ failed
        }
      }

      case ELt(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => {
                if (n1 < n2) VBool(true) else VBool(false)
              }
              case _ =>  VNil() // println("VInt failed");
            }
          }
          case _ =>  VNil() // println("ELT failed");
        }
      }

      case EGt(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case VInt(n1) => {
            true_eval(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => {
                if (n1 > n2) VBool(true) else VBool(false)
              }
              case _ =>VNil() // println("VInt failed");
            }
          }
          case _ =>  VNil() //println("ELT failed");
        }
      }

      case EIf(econd: Expr, et: Expr, ef: Expr) => {

        true_eval(econd, env_stack_in_true_eval, Nil) match {

          case VBool(boolean: Boolean) => boolean match {
            case true => true_eval(et, env_stack_in_true_eval, Nil)
            case false => true_eval(ef, env_stack_in_true_eval, Nil)
          }
          case _ => VNil() // println("EIf failed");
        }
      }

      case EPlus(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {

          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case VInt(n2) => VInt(n1 + n2)
            case _ => VNil() //println("EPlus failed");
          }
          case _ =>  VNil() // println("EPlus failed");
        }
      }

      case EMinus(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {

          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case VInt(n2) => VInt(n1 - n2)
            case _ => VNil() //println("EPlus failed"); V
          }
          case _ => VNil() // println("EPlus failed");
        }
      }

      case EMult(e1, e2) => {
        true_eval(e1, env_stack_in_true_eval, Nil) match {
          case VInt(n1) => true_eval(e2, env_stack_in_true_eval, Nil) match {
            case VInt(n2) => VInt(n1 * n2)
            case _ =>  VNil() // println("EPlus failed");
          }
          case _ => VNil() // println("EPlus failed");
        }
      }
      case _ => VNil() // println("Other failed");
    }
  }

  def myeval_memo(e: Expr): Val = {

    val myhash = collection.mutable.HashMap.empty[(Expr, List[EVbox]), Val];

    def true_eval_memo(e: Expr, env_stack_in_true_eval: Environment_Stack, arguments_in_true_eval: List[EVbox]): Val = {
      e match {
        case EApp(ef: Expr, eargs: List[Expr]) => {


          myhash.get((ef, evaluate_args(eargs, env_stack_in_true_eval))) match {

            case None => {

              ef match {
                case EFun(params: List[String], eb: Expr) => {
                  val result = true_eval_memo(ef, env_stack_in_true_eval, evaluate_args(eargs, env_stack_in_true_eval))
                  myhash.update((ef, evaluate_args(eargs, env_stack_in_true_eval)), result)
                  result
                }

                case EName(name) => {
                  val evaluated_args = evaluate_args(eargs, env_stack_in_true_eval)
                  val result = true_eval_memo(EName(name), env_stack_in_true_eval, evaluated_args)
                  myhash.update((ef, evaluate_args(eargs, env_stack_in_true_eval)), result)
                  result
                }

                case _ => {
                  def excecute_list_of_expr(x: List[Expr], formerVal: Val): Val = {
                    x match {
                      case Nil => formerVal
                      case hd :: tail => excecute_list_of_expr(tail, true_eval_memo(hd, env_stack_in_true_eval, Nil))
                    }
                  }
                  val intermediate_result = true_eval_memo(ef, env_stack_in_true_eval, Nil)
                  excecute_list_of_expr(eargs, intermediate_result)
                }
              }
            }
            case Some(value: Val) => value
          }
        }

        case EFun(params, eb) => {

          // 파라미터가 0도 아닌데, argument를 전달 받지 못했다는 것은 function 이
          // 반환되며 불려진 경우다.
          // EFun 이 사용되는 곳은 크게
          // 1) EApp 에서 - argument 전달
          // 2) def x EFun - 이 때 정의만 하기 때문에 evaluate 하지 않음. 고로 여기에 도달할 수 없음
          // 3) EFun 을 반환 할 때 - argument도 없다.
          // 따라서 parameter의 수가 0 개가 아닌데 argument가 전달되지 않았다면,
          // 함수를 반환하는 경우가 될 것 이다.

          if (params.nonEmpty && (arguments_in_true_eval == Nil)) {
            VFunc()
          }

          else {
            // 그게 아니라면 전달 받은 argument와 parameter를 결합하여 새로운 Environemnt를 만들고
            // 그 환경하에서 function body를 evaluate 한다.
            val params_env: Environment = env_maker_with_params_vals(params, arguments_in_true_eval)
            true_eval_memo(eb, params_env :: env_stack_in_true_eval, Nil)
          }
        }

        // name을 만났을 때 Value를 return하는 함수이다.
        case EName(x: String) => {

          @tailrec
          def stack_undwinder(env_in_stk_unwinder: Environment_Stack, x: String): (EVbox, Environment_Stack) = {
            env_in_stk_unwinder match {
              case Nil => (Valuebox(VNil()), Nil) //EName error: env_stack fully consumed w/o getting name
              case env_stk_hd :: env_stk_tail => {
                val result: Option[EVbox] = ev_finder(env_stk_hd, x)
                result match {
                  case None => stack_undwinder(env_stk_tail, x)
                  case Some(res) => (res, env_in_stk_unwinder)
                }
              }
            }
          }
          val stk_unwind_result = stack_undwinder(env_stack_in_true_eval, x)
          stk_unwind_result._1 match {
            case Valuebox(value) => value
            case Exprbox(expr) => true_eval_memo(expr, stk_unwind_result._2, arguments_in_true_eval)
          }
        }

        case EHd(el: Expr) => el match {
          case ECons(eh, et) => true_eval_memo(eh, env_stack_in_true_eval, Nil)
          case _ => VNil() //println("EHd fial");
        }

        case ETl(el: Expr) => el match {
          case ECons(eh, et) => true_eval(et, env_stack_in_true_eval, Nil)
          case _ => VNil() //println("EHd fial");
        }

        case EConst(c) => c match {
          case CInt(n) => VInt(n)
          case CTrue() => VBool(true)
          case CFalse() => VBool(false)
          case CNil() => VNil();
          case _ => VNil() //println("EConst fail");
        }

        case ELet(bs: List[Bind], eb: Expr) => {

          def EnvMaker(bs: List[Bind], former_scope: Environment_Stack, working_environment: Environment)
          : Environment = {

            bs match {
              case Nil => working_environment
              case (bkind, str, expr) :: tail => bkind match {
                case BDEF() => {
                  val new_env_element: (String, EVbox) = (str, Exprbox(expr))
                  val new_working_env = new_env_element :: working_environment
                  EnvMaker(tail, former_scope, new_working_env)
                }
                case BVAL() => {
                  val value_evaluated = true_eval_memo(expr, working_environment :: former_scope, Nil)
                  val new_env_element: (String, EVbox) = (str, Valuebox(value_evaluated))
                  val new_env = new_env_element :: working_environment
                  EnvMaker(tail, former_scope, new_env)
                }
              }
            }
          }

          val newly_added_scope = EnvMaker(bs, env_stack_in_true_eval, Nil)

          newly_added_scope match {
            case Nil => true_eval_memo(eb, env_stack_in_true_eval, Nil)
            case _ => true_eval_memo(eb, newly_added_scope :: env_stack_in_true_eval, Nil)
          }
        }

        case ECons(e1, e2) => {
          val val_1 = true_eval_memo(e1, env_stack_in_true_eval, Nil)
          val val_2 = true_eval_memo(e2, env_stack_in_true_eval, Nil)
          VPair(val_1, val_2)
        }

        case EEq(e1, e2) => {

          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

            case VInt(n1) => {
              true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
                case VInt(n2) => {
                  if (n1 == n2) VBool(true) else VBool(false)
                }
                case _ => VNil() //VInt failed
              }
            }
            case _ =>  VNil() // EEQ failed
          }
        }

        case ELt(e1, e2) => {
          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
            case VInt(n1) => {
              true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
                case VInt(n2) => {
                  if (n1 < n2) VBool(true) else VBool(false)
                }
                case _ =>  VNil() // println("VInt failed");
              }
            }
            case _ =>  VNil() // println("ELT failed");
          }
        }

        case EGt(e1, e2) => {
          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
            case VInt(n1) => {
              true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
                case VInt(n2) => {
                  if (n1 > n2) VBool(true) else VBool(false)
                }
                case _ =>VNil() // println("VInt failed");
              }
            }
            case _ =>  VNil() //println("ELT failed");
          }
        }

        case EIf(econd: Expr, et: Expr, ef: Expr) => {

          true_eval_memo(econd, env_stack_in_true_eval, Nil) match {

            case VBool(boolean: Boolean) => boolean match {
              case true => true_eval_memo(et, env_stack_in_true_eval, Nil)
              case false => true_eval_memo(ef, env_stack_in_true_eval, Nil)
            }
            case _ => VNil() // println("EIf failed");
          }
        }

        case EPlus(e1, e2) => {
          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

            case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => VInt(n1 + n2)
              case _ => VNil() //println("EPlus failed");
            }
            case _ =>  VNil() // println("EPlus failed");
          }
        }

        case EMinus(e1, e2) => {
          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {

            case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => VInt(n1 - n2)
              case _ => VNil() //println("EPlus failed"); V
            }
            case _ => VNil() // println("EPlus failed");
          }
        }

        case EMult(e1, e2) => {
          true_eval_memo(e1, env_stack_in_true_eval, Nil) match {
            case VInt(n1) => true_eval_memo(e2, env_stack_in_true_eval, Nil) match {
              case VInt(n2) => VInt(n1 * n2)
              case _ =>  VNil() // println("EPlus failed");
            }
            case _ => VNil() // println("EPlus failed");
          }
        }
        case _ => VNil() // println("Other failed");
      }
    }
    true_eval_memo(e, Nil, Nil)
  }


}
