import scala.lms.common._

trait LinearAlgebra extends Base with PrimitiveOps 
					with NumericOps with LiftNumeric 
					with FractionalOps {
	// Interface
	type Vector

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

	implicit def vec(s: Seq[Double]): Rep[Vector]

}


trait LinearAlgebraExp extends LinearAlgebra with BaseExp 
	  				   with SeqOpsExp with NumericOpsExp 
	  				   with PrimitiveOpsExp 
	  				   with FractionalOpsExp {
	// Implementation: I.e. how to generate an IR reperesentation
	override type Vector = Seq[Double]

	override implicit def vec(s: Seq[Double]): Rep[Vector] = unit(s)

	case class VectorScale(v: Exp[Vector], k: Exp[Double])
		extends Def[Vector]

	case class VectorAdd(v1: Exp[Vector], v2: Exp[Vector]) 
		extends Def[Vector]

	case class VectorDiv(v: Exp[Vector], k: Exp[Double])
		extends Def[Vector]

	override def vector_scale(v: Exp[Vector], k: Exp[Double]) = 
		toAtom(VectorScale(v, k))
	// TODO: What is toAtom - reread LMS paper

	override def vector_add(v1: Exp[Vector], v2: Exp[Vector]) = 
		toAtom(VectorAdd(v1, v2))

	override def vector_div(v: Exp[Vector], k: Exp[Double]) =
		toAtom(VectorDiv(v, k))
}

trait LinearAlgebraExpOpt extends LinearAlgebraExp {
	override def vector_scale(v: Exp[Vector], k: Exp[Double]) = 
		// TODO: Rewrite to use Numeric instead of Double
		(v, k) match {
			case (v, Const(k)) if k == 1.0 => v
			case _ => super.vector_scale(v, k)
		}

	private def is_zeroes(v: Vector): Boolean =
		v.forall(_ == 0.0)

	override def vector_add(v1: Exp[Vector], v2: Exp[Vector]) =
		(v1, v2) match {
			case (v1, Const(v2)) if is_zeroes(v2) => v1
			case (Const(v1), v2) if is_zeroes(v1) => v2
			case _ => super.vector_add(v1, v2)
		}
}

trait ScalaGenLinearAlgebra extends ScalaGenBase {
	val IR: LinearAlgebraExpOpt
	import IR._

	override def emitNode(sym: Sym[Any], 
						  node: Def[Any]): Unit = node match {
		case VectorScale(v, k) => {
			emitValDef(sym, src"$v.map(_ * $k)")
		}

		case VectorAdd(v1, v2) => {
			emitValDef(sym, src"($v1, $v2).zipped.map(_ + _)")
		}

		case VectorDiv(v, k) => {
			emitValDef(sym, src"$v.map(_ / $k)")
		}
		case _ => super.emitNode(sym, node)
		
	}
}


/*trait CGenLinearAlgebra extends CLikeGenBase {
	val IR: LinearAlgebraExpOpt
	import IR._

	override def emitNode(sym: Sym[Any],
						  node: Def[Any]): Unit = node match {
		// This is different to the Scala implementation as 
		// it mutates the vector
		// Also the behaviour differes if the vectors are different
		// lengths

		case SeqNew(xs) => {
			emitValDef(sym, 
				)
		}
		case VectorScale(v, k) => {
			emitValDef(sym,
				src"""int vec_len = length($v)
		   	  		  for (int i = 0; i < vec_len; i++) {
		   				$v[i] *= $k;
		   			}
		   		   """
		   	)
		}
		case VectorDiv(v, k) => {
			emitValDef(sym,
				src"""int vec_len = length($v)
		   	  		  for (int i = 0; i < vec_len; i++) {
		   				$v[i] /= $k;
		   			}
		   		   """
		   	)
		}

		case VectorAdd(v1, v2) => {
			// Hope the vectors are the same length!
			// 
			src"""int vec_len = length($v1)
			for (int i = 0; i < vec_len; i++) {
				$v1[i] += $v2[i]
			}
			"""
		}
	}
}
*/

trait Prog extends LinearAlgebra {
	def f(v1: Rep[Vector]): Rep[Vector] = 
		((v1 + Seq(0.0, 1.0, 0.0)) * 5.0) + Seq(2.0, 3.0)
}

object LinAlg {
	def main(args: Array[String]): Unit = {
		println("Hello LMS!")

		val prog = new Prog with LinearAlgebraExpOpt with EffectExp 
							with CompileScala {
			// Is CompileScala the key?
			self =>	
			override val codegen = new ScalaGenEffect 
								   with ScalaGenLinearAlgebra {
				// This line is still very confusing
				val IR: self.type = self
			}
			codegen.emitSource(f, "F", new java.io.PrintWriter(System.out))
		}
		// TODO: What is the 'EffectExp'
	}
}