package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

// The variables have been named to be similar to be the ones used in the lectures
public class PredicationVisitor extends DefaultVisitor {

    // Default variable type is int
    public static final String DEFAULT_VARIABLE_TYPE = "int";

    // Prefix for the predication name
    // The variables used will be named as $PRED0, $PRED1, etc.
    private static final String BASE_NAME = "$PRED";

    // The global predicate initialized to true
    private Expr GLOBAL_PRED =  new IntLiteral(1);

    // A stack is used to store the local predicate
    // The top of the stack stores P and is initially true
    private Stack<Expr> basePredicateStack = new Stack<Expr>();

    // Store the counter for the predicate
    private int baseInt = 0;

	public PredicationVisitor() {
        super(true);
        basePredicateStack.push(new IntLiteral(1));
	}

    // Gets the next predicate name
    private String getNextName(){
        return BASE_NAME + (baseInt++);
    }

	@Override
	public Object visit(IfStmt ifStmt ) {
        Expr e = ifStmt.getCondition();

        // p && e
        Expr q = new BinaryExpr(BinaryExpr.LAND,basePredicateStack.peek(), e);

        // p && !e
        Expr r = new BinaryExpr(BinaryExpr.LAND,basePredicateStack.peek(),new UnaryExpr(UnaryExpr.LNOT, e));

        // Declare P and Q variables and assign values appropriately.
        DeclRef Q = new DeclRef(getNextName());
        DeclRef R = new DeclRef(getNextName());
        Decl declareQ = new Decl(Q.getName(), DEFAULT_VARIABLE_TYPE);
        Decl declareR = new Decl(R.getName(), DEFAULT_VARIABLE_TYPE);

        // Q = p && !e
        AssignStmt assignQ = new AssignStmt(Q, q);
        // R = p && !e
        AssignStmt assignR = new AssignStmt(R, r);

        // Push Q and make it the current local predicate
        // Then visit the if branch
        basePredicateStack.push(Q);
        Stmt qBranch = (Stmt)visit(ifStmt.getThenStmt());
        // Pop it out so that it is not the current local predicate
        basePredicateStack.pop();

        // Push R and make it the current local predicate
        // Then visit the else branch
        basePredicateStack.push(R);
        Stmt rBranch = (Stmt)visit(ifStmt.getElseStmt());
        // Pop it out so that it is not the current local predicate
        basePredicateStack.pop();

        // Collate all the statements and combine them to return a block statement
        List<Stmt> statements = new ArrayList<Stmt>();
        statements.add(declareQ);
        statements.add(declareR);
        statements.add(assignQ);
        statements.add(assignR);
        statements.add(qBranch);
        statements.add(rBranch);

        return super.visit(new BlockStmt(statements,ifStmt));
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
        // ~(p && G) || E  is same as (P && G) -> E
        BinaryExpr implication = new BinaryExpr(BinaryExpr.LOR, new UnaryExpr(UnaryExpr.LNOT , gAndP()), assertStmt.getCondition());

        return super.visit(new AssertStmt(implication , assertStmt));
	}

	@Override
	public Object visit(AssignStmt assignment) {
        // Replace x = y by x = P && G ? y :x
        DeclRef x = assignment.getLhs();
        TernaryExpr ternaryExpression = new TernaryExpr(gAndP(), assignment.getRhs(), x);

        return super.visit(new AssignStmt(x, ternaryExpression, assignment));
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {

        // ~(p && G) || E  is same as (P && G) -> E
        Expr condition = assumeStmt.getCondition();
        BinaryExpr binaryExpr = new BinaryExpr(BinaryExpr.LOR,
                                new UnaryExpr(UnaryExpr.LNOT, gAndP()),
                                condition);

        // Get a fresh variable A
        DeclRef A = new DeclRef(getNextName());
        Decl declareA= new Decl(A.getName(), DEFAULT_VARIABLE_TYPE);

        // A = (g && p) -> E
        AssignStmt assignA = new AssignStmt(A, binaryExpr);

        // G = G && A
        GLOBAL_PRED = new BinaryExpr(BinaryExpr.LAND, GLOBAL_PRED, A);

        return super.visit(new BlockStmt(new Stmt[]{declareA, assignA},assumeStmt));
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
        DeclRef x = havocStmt.getVariable();

        // Get a fresh variable called h
        DeclRef h = new DeclRef(getNextName());
        Decl declareH = new Decl(h.getName(), DEFAULT_VARIABLE_TYPE);

        // (g && p) ? h : x
        TernaryExpr ternaryExpression = new TernaryExpr(gAndP(), h, x);

        // x = (g && p) ? h : x
        AssignStmt assignX = new AssignStmt(x, ternaryExpression);

        return super.visit(new BlockStmt(new Stmt[]{declareH, assignX}, havocStmt));
	}

    // Returns G && P
    private Expr gAndP(){
        return new BinaryExpr(BinaryExpr.LAND,GLOBAL_PRED, basePredicateStack.peek());
    }
}
