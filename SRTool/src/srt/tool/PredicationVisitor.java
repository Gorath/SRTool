package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.Random;
import java.util.Stack;

public class PredicationVisitor extends DefaultVisitor {
    private Expr GLOBAL_PRED =  new IntLiteral(1);
    private Stack<Expr> stack = new Stack<Expr>();
    private final String baseName = "$PRED";
    private int baseInt = 0;

	public PredicationVisitor() {
        super(true);
        stack.push(GLOBAL_PRED);
	}

    private String getNextName(){
        return  baseName + (baseInt++);
    }

	@Override
	public Object visit(IfStmt ifStmt ) {
        Expr e = ifStmt.getCondition();
        Stmt q = ifStmt.getThenStmt();
        Stmt r = ifStmt.getElseStmt();

        return new TernaryExpr(e,null,null,ifStmt);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {

        return super.visit(assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
		return super.visit(assignment);
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
        Expr condition = assumeStmt.getCondition();
        DeclRef A = new DeclRef( getNextName());
        Decl declareStmnt = new Decl(A.getName(),"int");
        BinaryExpr binaryExpr = new BinaryExpr(BinaryExpr.LOR,
                                new UnaryExpr(UnaryExpr.LNOT,gAndP()),
                                condition);
        AssignStmt assign = new AssignStmt(A ,binaryExpr);
        GLOBAL_PRED = new BinaryExpr(BinaryExpr.LAND, GLOBAL_PRED, A);
        return new BlockStmt(new Stmt[]{declareStmnt,assign},assumeStmt);
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
         DeclRef x = havocStmt.getVariable();
         DeclRef h = new DeclRef( getNextName());
         Decl declareStmnt = new Decl(h.getName(),"int");
         TernaryExpr te = new TernaryExpr(gAndP(),h,x);
         AssignStmt assign = new AssignStmt(x ,te);
         return new BlockStmt(new Stmt[]{declareStmnt,assign},havocStmt);
	}

    private BinaryExpr gAndP(){
         return new BinaryExpr(BinaryExpr.LAND,GLOBAL_PRED,stack.peek());
    }
}
