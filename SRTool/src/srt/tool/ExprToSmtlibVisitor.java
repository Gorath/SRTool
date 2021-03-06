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


    // Ensured everything returns bitvectors
    // Carefully referred to the documentation and extensively tested
	@Override
	public String visit(BinaryExpr expr) {
		String operator ;
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
                operator = "(bvshl %s %s)";
                break;
			case BinaryExpr.MOD:
                operator = "(bvsmod %s %s)";
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
                operator = "(tobv32 (and  (tobool %s) (tobool %s)))";
                break;
			case BinaryExpr.LOR:
                operator = "(tobv32 (or  (tobool %s) (tobool %s)))";
                break;
			case BinaryExpr.GEQ:
                operator = "(tobv32 (bvsge %s %s))";
                break;
			case BinaryExpr.GT:
                operator = "(tobv32 (bvsgt %s %s))";
                break;
			case BinaryExpr.LEQ:
                operator = "(tobv32 (bvsle %s %s))";
                break;
			case BinaryExpr.LT:
                operator = "(tobv32 (bvslt %s %s))";
                break;
			case BinaryExpr.NEQUAL:
                operator = "(tobv32 (not (= %s %s)))";
				break;
			case BinaryExpr.EQUAL:
                    operator = "(tobv32 (= %s %s))";
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
        // Converting int to bitvector
        String s = String.format("%08x", intLiteral.getValue());
		return "#x" + s;
	}

	@Override
	public String visit(TernaryExpr ternaryExpr) {
		return String.format("(ite (tobool %s) %s %s )" ,
                    this.visit(ternaryExpr.getCondition()),
                    this.visit(ternaryExpr.getTrueExpr()),
                    this.visit(ternaryExpr.getFalseExpr()));
	}

    // Ensured everything returns bitvectors
    // Carefully referred to the documentation and extensively tested the unary operations
	@Override
	public String visit(UnaryExpr unaryExpr) {
		String operator ;
		switch(unaryExpr.getOperator())
		{
		case UnaryExpr.UMINUS:
			operator = "(bvneg %s)";
			break;
		case UnaryExpr.UPLUS:
            operator = "%s";
			break;
		case UnaryExpr.LNOT:
            operator = "(tobv32 (not (tobool %s)))";
			break;
		case UnaryExpr.BNOT:
            operator = "(bvnot %s)";
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