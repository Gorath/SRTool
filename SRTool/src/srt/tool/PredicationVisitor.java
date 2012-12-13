package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

public class PredicationVisitor extends DefaultVisitor {
    // The global predicate initialized to true;
    private Expr GLOBAL_PRED =  new IntLiteral(1);
    // A stack is used to store the current value for p. it initially contains true;
    private Stack<Expr> stack = new Stack<Expr>();
    // The variables used will be named  as $PRED0 $PRED1 ...
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
        // q = p && e
        Expr q = new BinaryExpr(BinaryExpr.LAND,stack.peek(),e);
        // r = p && e
        Expr r = new BinaryExpr(BinaryExpr.LAND,stack.peek(),new UnaryExpr(UnaryExpr.LNOT , e ));
        // declare P and Q variables and assign values appropriately.
        DeclRef Q = new DeclRef( getNextName());
        DeclRef R = new DeclRef( getNextName());
        Decl declareQ = new Decl(Q.getName(),"int");
        Decl declareR = new Decl(R.getName(),"int");
        AssignStmt assignQ = new AssignStmt(Q ,q);
        AssignStmt assignR = new AssignStmt(R ,r);
        // push q and visit the if branch.
        stack.push(Q);
        Stmt qBranch = (Stmt)visit(ifStmt.getThenStmt());
        stack.pop();
        // push r and visit the then branch.
        stack.push(R);
        Stmt rBranch = (Stmt)visit(ifStmt.getElseStmt());
        stack.pop();
        // collect all the statements and combine them to return a  block statement.
        List<Stmt>  statements = new ArrayList<Stmt>();
        statements.add(declareQ);
        statements.add(declareR);
        statements.add(assignQ);
        statements.add(assignR);
        statements.add(qBranch);
        statements.add(rBranch);
        return new BlockStmt(statements,ifStmt);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
         // return not ( p and G ) or  E  which is the same as P and G implies E
        BinaryExpr implication = new BinaryExpr(BinaryExpr.LOR , new UnaryExpr( UnaryExpr.LNOT , gAndP()) ,assertStmt.getCondition());
       return new AssertStmt(implication , assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
        //replace x = y by  x = P && G ? y :x
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
        //A stores  ( g and p )  => E
        AssignStmt assign = new AssignStmt(A ,binaryExpr);
        //Global pred = global pred && A
        GLOBAL_PRED = new BinaryExpr(BinaryExpr.LAND, GLOBAL_PRED, A);
        //return A
        return new BlockStmt(new Stmt[]{declareStmnt,assign},assumeStmt);
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
         DeclRef x = havocStmt.getVariable();
         // get a fresh variable called h
         DeclRef h = new DeclRef(getNextName());
         Decl declareStmnt = new Decl(h.getName(),"int");
         TernaryExpr te = new TernaryExpr(gAndP(),h,x);
         // x =  ( g and p ) ? h : x
         AssignStmt assign = new AssignStmt(x ,te);
         return new BlockStmt(new Stmt[]{declareStmnt,assign},havocStmt);
	}

    private Expr gAndP(){
        //returns g and p.
        return new BinaryExpr(BinaryExpr.LAND,GLOBAL_PRED,stack.peek());
    }
}
