package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;
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
        Expr q = new BinaryExpr(BinaryExpr.LAND,stack.peek(),e);
        Expr r = new BinaryExpr(BinaryExpr.LAND,stack.peek(),new UnaryExpr(UnaryExpr.LNOT , e ));
        DeclRef Q = new DeclRef( getNextName());
        DeclRef R = new DeclRef( getNextName());
        Decl declareQ = new Decl(Q.getName(),"int");
        Decl declareR = new Decl(R.getName(),"int");
        AssignStmt assignQ = new AssignStmt(Q ,q);
        AssignStmt assignR = new AssignStmt(R ,r);
        stack.push(Q);
        Stmt qObject = (Stmt)visit(ifStmt.getThenStmt());
        stack.pop();
        stack.push(R);
        Stmt rObject = (Stmt)visit(ifStmt.getElseStmt());
        stack.pop();
        List<Stmt>  statements = new ArrayList<Stmt>();
        statements.add(declareQ);
        statements.add(declareR);
        statements.add(assignQ);
        statements.add(assignR);
        statements.add(qObject);
        statements.add(rObject);
        return new BlockStmt(statements,ifStmt);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
       BinaryExpr implication = new BinaryExpr(BinaryExpr.LOR , new UnaryExpr( UnaryExpr.LNOT , gAndP()) ,assertStmt.getCondition());
       return new AssertStmt(implication , assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
        DeclRef x = assignment.getLhs();
        TernaryExpr te = new TernaryExpr(gAndP(),assignment.getRhs(),x);
        return new AssignStmt(x ,te,assignment);
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
         DeclRef h = new DeclRef(getNextName());
         Decl declareStmnt = new Decl(h.getName(),"int");
         TernaryExpr te = new TernaryExpr(gAndP(),h,x);
         AssignStmt assign = new AssignStmt(x ,te);
         return new BlockStmt(new Stmt[]{declareStmnt,assign},havocStmt);
	}

    private Expr gAndP(){
        return new BinaryExpr(BinaryExpr.LAND,GLOBAL_PRED,stack.peek());
    }
}
