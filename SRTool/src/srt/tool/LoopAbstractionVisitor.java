package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {

        List<Stmt> statements = new ArrayList<Stmt>();

        /************ Assert of all invariants ********/
        List<Stmt> assertions =  new ArrayList<Stmt>();
        List<Stmt> assumptions =  new ArrayList<Stmt>();
        generateAssertionsAndAssumptions(assertions,assumptions,whileStmt);

        statements.addAll(assertions);


        /************       Havoc modset       ********/
        Stmt whileBody = whileStmt.getBody();
        ArrayList<Node> modset = whileBody.getModSet();
        ArrayList<DeclRef> filteredModset =  new ArrayList<DeclRef>();

        /*******************REMOVE DUPLICATES*************/
        for ( Node n : modset){
            boolean duplicate = false;
            for ( Node existing : filteredModset){
                 if (((DeclRef)existing).getName().equals(((DeclRef)n).getName()) ){
                     duplicate = true;
                     break;
                 }
            }
            if (!duplicate) filteredModset.add((DeclRef)n);
        }


        List<Stmt> havocs = new ArrayList<Stmt>();
        for (DeclRef variable :filteredModset){
            havocs.add(new HavocStmt(variable));
        }

        statements.addAll(havocs);

        /************   Assume the invariants  ********/
        statements.addAll(assumptions);

        /************  Execute loop body once  ********/
        List<Stmt> ifBody = new ArrayList<Stmt>();
        if ( whileBody instanceof  BlockStmt){
            ifBody.addAll(((BlockStmt)whileBody).getStmtList().getStatements());
        }   else{
            ifBody.add(whileBody);
        }
        ifBody.addAll(assertions);
        ifBody.add(new AssumeStmt(new IntLiteral(0)));

        Stmt ifStmt = new IfStmt(whileStmt.getCondition(),new BlockStmt(ifBody),new EmptyStmt(), whileStmt);

        statements.add(ifStmt);

        return super.visit(new BlockStmt(statements,whileStmt));
	}

    private void generateAssertionsAndAssumptions(List<Stmt> assertions, List<Stmt> assumptions , WhileStmt whileStmt){
        ExprList invariantsList = whileStmt.getInvariantList();
        for ( Expr e : invariantsList.getExprs()){
               assertions.add(new AssertStmt( e ,e ));
               assumptions.add(new AssumeStmt(e, e));
        }
    }

}
