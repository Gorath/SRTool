package srt.tool;

import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.IntLiteral;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class ExprToSmtlibVisitor extends DefaultVisitor {
	
	public ExprToSmtlibVisitor() {
		super(false);
	}

	@Override
	public String visit(BinaryExpr expr) {
		String operator = null;
		switch(expr.getOperator())
		{
			case BinaryExpr.ADD:
				operator = "(bvadd %s %s)";
				break;
			case BinaryExpr.BAND:
                operator = "(bvand %s %s)";
                break;
			case BinaryExpr.BOR:
                operator = "(bvor %s %s)";
                break;
			case BinaryExpr.BXOR:
                operator = "(bvxor %s %s)";
                break;
			case BinaryExpr.DIVIDE:
                operator = "(bvsdiv %s %s)";
                break;
			case BinaryExpr.LSHIFT:
                operator = "(bvshl %s #x10000000)";
                break;
			case BinaryExpr.MOD:
                operator = "(bvlshr %s %s)";
                break;
			case BinaryExpr.MULTIPLY:
                operator = "(bvmul %s %s)";
                break;
			case BinaryExpr.RSHIFT:
                operator = "(bvashr %s %s)";
                break;
			case BinaryExpr.SUBTRACT:
                operator = "(bvsub   %s %s)";
                break;
			case BinaryExpr.LAND:
                operator = "(bvsdiv  %s %s)";

                break;
			case BinaryExpr.LOR:
                operator = "(bvsdiv  %s %s)";

                break;
			
			case BinaryExpr.GEQ:
                operator = "(bvsdiv  %s %s)";

                break;
			case BinaryExpr.GT:
                operator = "(bvsdiv  %s %s)";

                break;
			case BinaryExpr.LEQ:
                operator = "(bvsdiv  %s %s)";

                break;
			case BinaryExpr.LT:
                operator = "(bvsdiv  %s %s)";

                break;
			case BinaryExpr.NEQUAL:
				break;
			case BinaryExpr.EQUAL:
                if (expr.getTokenInfo().toString().equals("==")) {
                    operator = "(ite (and %s %s) (_ bv1 32)(_ bv0 32))";
                } else {
                    operator = "(= %s %s)";
                }
				break;
			default:
				throw new IllegalArgumentException("Invalid binary operator");
		}
		
		return String.format(operator, visit(expr.getLhs()), visit(expr.getRhs()));
		
	}

	@Override
	public String visit(DeclRef declRef) {
		return declRef.getName();
	}

	@Override
	public String visit(IntLiteral intLiteral) {
        String s = String.format("%08x", intLiteral.getValue());
		return "#x" + s;
	}

	@Override
	public String visit(TernaryExpr ternaryExpr) {
		return null;
	}

	@Override
	public String visit(UnaryExpr unaryExpr) {
		String operator = null;
		switch(unaryExpr.getOperator())
		{
		case UnaryExpr.UMINUS:
			operator = "(bvneg %s)";
			break;
		case UnaryExpr.UPLUS:
			break;
		case UnaryExpr.LNOT:
			break;
		case UnaryExpr.BNOT:
			break;
		default:
			throw new IllegalArgumentException("Invalid binary operator");
		}
		
		return String.format(operator, visit(unaryExpr.getOperand()));
	}
	
	
	/* Overridden just to make return type String. 
	 * @see srt.ast.visitor.DefaultVisitor#visit(srt.ast.Expr)
	 */
	@Override
	public String visit(Expr expr) {
		return (String) super.visit(expr);
	}
	
	

}