import scala.lms.common._
import java.io._

trait VectorOps extends Base with PrimitiveOps
					with NumericOps with LiftNumeric
					with FractionalOps with TupleOps
          with ArrayOps {
	// Interface
	type Vector

  implicit def repVectorToVectorOps(v: Rep[Vector]) = new VectorOpsCls(v)

	// Base trait contains Rep[T], an abstract type member
	// And unit[T](x: T): Rep[T], used to lift values
	def infix_*(v: Rep[Vector], k: Rep[Double]): Rep[Vector] =
		vector_scale(v, k)
	def vector_scale(v: Rep[Vector], k: Rep[Double]): Rep[Vector]

	def infix_/(v: Rep[Vector], k: Rep[Double]): Rep[Vector] =
		vector_div(v, k)
	def vector_div(v: Rep[Vector], k: Rep[Double]): Rep[Vector]

	def infix_+(v1: Rep[Vector], v2: Rep[Vector]): Rep[Vector] =
		vector_add(v1, v2)
	def vector_add(v1: Rep[Vector], v2: Rep[Vector]): Rep[Vector]

  def vector_apply(v: Rep[Vector], i: Rep[Int]): Rep[Double]

  class VectorOpsCls(v: Rep[Vector]) {
    def apply(n: Rep[Int]) = vector_apply(v, n)
  }
  def new_vector(xs: Rep[Double]*): Rep[Vector]
}



trait VectorOpsExp extends VectorOps with BaseExp
	  				   with SeqOpsExp with NumericOpsExp with PrimitiveOpsExp
	  				   with FractionalOpsExp with TupleOpsExp
               with ArrayOpsExp {
	// Implementation: I.e. how to generate an IR reperesentation

  // TODO: Why is this still here. Remove
  override type Vector = (Seq[Double], Int)

	case class VectorScale(v: Exp[Vector], k: Exp[Double])
		extends Def[Vector]

	case class VectorAdd(v1: Exp[Vector], v2: Exp[Vector])
		extends Def[Vector]

	case class VectorDiv(v: Exp[Vector], k: Exp[Double])
		extends Def[Vector]

  case class NewVector(l: Int, xs: Seq[Exp[Double]])
    extends Def[Vector]

  case class VectorApply(v: Rep[Vector], i: Rep[Int])
    extends Def[Double]

	override def vector_scale(v: Exp[Vector], k: Exp[Double]) =
		toAtom(VectorScale(v, k))

	override def vector_add(v1: Exp[Vector], v2: Exp[Vector]) =
		toAtom(VectorAdd(v1, v2))

	override def vector_div(v: Exp[Vector], k: Exp[Double]) =
		toAtom(VectorDiv(v, k))

  override def new_vector(xs: Exp[Double]*) =
    toAtom(NewVector(xs.length, xs))

  override def vector_apply(v: Rep[Vector], i: Rep[Int]) =
    toAtom(VectorApply(v, i))
}

trait VectorOpsExpOpt extends VectorOpsExp {
	override def vector_scale(v: Exp[Vector], k: Exp[Double]) =
		// TODO: Rewrite to use Numeric instead of Double
		(v, k) match {
			case (v, Const(k)) if k == 1.0 => v
			case _ => super.vector_scale(v, k)
		}

	private def is_zeroes(vec_with_length: Vector): Boolean =
		vec_with_length._1.forall(_ == 0.0)

	override def vector_add(v1: Exp[Vector], v2: Exp[Vector]) =
		(v1, v2) match {
			case (v1, Const(v2)) if is_zeroes(v2) => v1
			case (Const(v1), v2) if is_zeroes(v1) => v2
			case _ => super.vector_add(v1, v2)
		}
}

trait ScalaGenVectorOps extends ScalaGenBase {
	val IR: VectorOpsExpOpt
	import IR._

	override def emitNode(sym: Sym[Any],
						  node: Def[Any]): Unit = node match {
		case VectorScale(v, k) => {
			emitValDef(sym, src"$v._1.map(_ * $k)")
		}

		case VectorAdd(v1, v2) => {
			emitValDef(sym, src"($v1._1, $v2._1).zipped.map(_ + _)")
		}

		case VectorDiv(v, k) => {
			emitValDef(sym, src"$v._1.map(_ / $k)")
		}
		case _ => super.emitNode(sym, node)
	}
}


trait CGenVectorOps extends CGenTupleOps
  with CGenPrimitiveOps {  // TODO: Why do we need CGenTupleOps
  // To maintain C immutability, we malloc new vectors for every operation.
  // This leaks memory everywhere.
	val IR: VectorOpsExpOpt
	import IR._

  private def initialize_empty_vector(sym: Sym[Any], vec: Exp[Vector]): Unit = {
    emitValDef(sym, "malloc(sizeof(Tuple2SeqDoubleInt))")
    stream.println(src"""
$sym->_1 = malloc(sizeof(double) * $vec->_2);
$sym->_2 = $vec->_2;
    """)
  }

	override def emitNode(sym: Sym[Any],
						  node: Def[Any]): Unit = {
    node match {
    case NewVector(k, xs) => {
      emitValDef(sym, "malloc(sizeof(Tuple2SeqDoubleInt))");
      stream.println(f"""
${quote(sym)}->_2 = $k;
${quote(sym)}->_1 = malloc(sizeof(double) * $k);"""
      )
      for (i <- 0 to k-1) {
        stream.println(f"""
${quote(sym)}->_1[$i] = ${quote(xs(i))};"""
)
      }

    }

		case VectorScale(v, k) => {
      initialize_empty_vector(sym, v)
			stream.println(src"""
for (int i = 0; i < $v->_2; i++) {
		$sym->_1[i] =  $v->_1[i] * $k;
}
		    """)
		}
		case VectorDiv(v, k) => {
      initialize_empty_vector(sym, v)
      stream.println(src"""
for (int i = 0; i < $v->_2; i++) {
  $sym->_1[i] = $v->_1[i] / $k;
}
      """)
		}

		case VectorAdd(v1, v2) => {
			// Hope the vectors are the same length!
			//
      initialize_empty_vector(sym, v2);
			stream.println(src"""
for (int i = 0; i < $v2->_2; i++) {
   $sym->_1[i] = $v1->_1[i] + $v2->_1[i];
}
			     """)
     }

     case VectorApply(v, i) => {
       emitValDef(sym, src"$v->_1[$i]")
     }

    case _ => {
      super.emitNode(sym, node)
    }
	}
}
  override def emitSource[A:Typ](args: List[Sym[_]], body: Block[A],
                                 functionName: String, out: java.io.PrintWriter) = {
      withStream(out) {
        stream.println("""
          typedef struct _Tuple2SeqDoubleInt {
            double *_1;
            int _2;
          } Tuple2SeqDoubleInt;

          double F(Tuple2SeqDoubleInt *x0);

          int main(int argc, char *argv[]) {
            Tuple2SeqDoubleInt *v = malloc(sizeof(Tuple2SeqDoubleInt));
            v->_2 = 3;
            v->_1 = malloc(sizeof(double) * 3);
            v->_1[0] = 1.0; v->_1[1] = 2.0; v->_1[2] = 4.0;
            F(v);
            return 0;
          }
        """)
      }
      super.emitSource[A](args, body, functionName, out)
  }
}

trait Prog extends VectorOps {
	def f(v1: Rep[Vector]): Rep[Double] = {
		val v = (v1 + new_vector(0.0, 1.0 * 4.0, 0.0) * 5.0) + new_vector(2.0, 3.0, 4.0)
    v(1) + v(2) + v(3)
  }
}

object LinAlg {
	def main(args: Array[String]): Unit = {
		val prog = new Prog with VectorOpsExpOpt with EffectExp {
			self =>
			 val codegen = new CGenVectorOps {
				val IR: self.type = self
			}
      // Hack to get a pointer
			codegen.emitSource(f, "F", new java.io.PrintWriter(new File("out.c")))
		}
	}
}
