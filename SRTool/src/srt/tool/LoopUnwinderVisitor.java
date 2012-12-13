package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopUnwinderVisitor extends DefaultVisitor {

	private boolean unwindingAssertions;
	private int defaultUnwindBound;

	public LoopUnwinderVisitor(boolean unwindingAssertions,
			int defaultUnwindBound) {
		super(true);
		this.unwindingAssertions = unwindingAssertions;
		this.defaultUnwindBound = defaultUnwindBound;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {


        AssertStmt loopAssert = new AssertStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()),whileStmt);
        AssumeStmt loopAssume = new AssumeStmt(new UnaryExpr(UnaryExpr.LNOT,whileStmt.getCondition()));

        Stmt[] statementArray;
        if (unwindingAssertions) {
            statementArray = new Stmt[2];
            statementArray[0] = loopAssert;
            statementArray[1] = loopAssume;
        } else {
            statementArray = new Stmt[1];
            statementArray[0] = loopAssume;
        }

        Stmt blockStatementBase = new BlockStmt(statementArray);
        Stmt whileBlock = whileStmt.getBody();

        for (int i = 0; i < whileStmt.getBound().getValue(); i++) {      // Check if getbound is null

            blockStatementBase = new BlockStmt(new Stmt[]{whileBlock,blockStatementBase});

            blockStatementBase = new IfStmt(whileStmt.getCondition(), blockStatementBase , new EmptyStmt());

        }

        Stmt w2 = new BlockStmt(new Stmt[]{blockStatementBase},whileBlock);

        return super.visit(w2);

        //return super.visit(whileStmt);

	}

}
