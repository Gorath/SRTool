package srt.tool;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.Tree;

import srt.ast.Program;
import srt.ast.visitor.impl.Checker;
import srt.ast.visitor.impl.MakeBlockVisitor;
import srt.ast.visitor.impl.PrinterVisitor;
import srt.exec.SMTQuery;
import srt.parser.SimpleCParserUtil;
import srt.tool.exception.CheckerExpception;
import srt.tool.exception.SMTSolverTimeoutException;
import srt.tool.exception.UnknownResultException;


public class SRTool {
    private String inputFile;
    private CLArgs clArgs;

    public SRTool(String inputFile, CLArgs clArgs) {
        super();
        this.inputFile = inputFile;
        this.clArgs = clArgs;
    }

    public List<AssertionFailure> go() throws IOException,
            RecognitionException, CheckerExpception, InterruptedException,
            SMTSolverTimeoutException, UnknownResultException {

        // Parse input Simple C file to AST
        Program p = SimpleCParserUtil.createAST(inputFile);

        // Add blocks to make things simpler
        // E.g. if(c) stmt; becomes if(c) {stmt;} else {}
        p = (Program) new MakeBlockVisitor().visit(p);

        // Do basic checks
        // E.g. Variables declared before use
        // no duplicate local variables
        Checker checker = new Checker();
        boolean success = checker.check(p);
        if (!success) {
            throw new CheckerExpception(checker.getCheckerError());
        }

        // Checks whether abstract loop abstraction is turned on
        if (clArgs.abstractLoops) {
            p = (Program) new LoopAbstractionVisitor().visit(p);
        } else {
            p = (Program) new LoopUnwinderVisitor(clArgs.unwindingAssertions,
                    clArgs.unwindDepth).visit(p);
        }

        // Carries out predication on the program
        p = (Program) new PredicationVisitor().visit(p);

        // Carries out ssa renaming on the program
        p = (Program) new SSAVisitor().visit(p);

        // Output the program as text after being transformed (for debugging)
        // Comment the code below to hide the output
        String programText = new PrinterVisitor().visit(p);
        System.out.println(programText);

        // Collect the constraint expressions and variable names
        CollectConstraintsVisitor collectConstraintsVisitor = new CollectConstraintsVisitor();
        collectConstraintsVisitor.visit(p);

        // Stores the assertion failures
        List<AssertionFailure> assertionFailures = new ArrayList<AssertionFailure>();

        // Stop here if there are no assertions (properties) to check
        if (collectConstraintsVisitor.propertyExprs.size() == 0) {
            System.out.println("No asserts! Stopping.");
            return assertionFailures;
        }

        // Convert constraints to SMTLIB string
        SMTLIBConverter converter = new SMTLIBConverter(collectConstraintsVisitor.variableNames,
                collectConstraintsVisitor.transitionExprs, collectConstraintsVisitor.propertyExprs);
        String smtQuery = converter.getQuery();

        // Submit query to SMT solver
        SMTQuery query = new SMTQuery(smtQuery, clArgs.timeout * 1000);
        String queryResult = query.go();
        if (queryResult == null) {
            throw new SMTSolverTimeoutException("Timeout!");
        }
        System.out.println("--SMT COMPLETE--");

        // Report the assertions that can be violated
        handleAssertionFailures(assertionFailures, collectConstraintsVisitor, queryResult);

        return assertionFailures;
    }

    // This method populates the assertion failures
    private void handleAssertionFailures(List<AssertionFailure> result, CollectConstraintsVisitor collectConstraintsVisitor, String queryResult) throws UnknownResultException {
        if (queryResult.startsWith("sat")) {

            List<Integer> indexesFailed = getPropertiesThatFailed(queryResult);

            // for all the properties that have failed, we get the index and report the failure
            for (Integer anIndexesFailed : indexesFailed) {
                Tree tree = collectConstraintsVisitor.propertyNodes.get(anIndexesFailed).getTokenInfo();
                // Uncomment the code below to see which assertions failed (used for debugging)
                // System.out.printf("Assertion failure on line:%s column:%s .\n", tree.getLine(), tree.getCharPositionInLine());
                result.add(new AssertionFailure(tree));
            }

        } else if (!queryResult.startsWith("unsat")) {
            throw new UnknownResultException();
        }
    }


    // Returns the indexes of the properties which returned false
    private List<Integer> getPropertiesThatFailed(String queryResult) {
        List<Integer> indexes = new ArrayList<Integer>();

        // Uses REGEX to correctly detect the indexes
        Pattern pattern = Pattern.compile("(\\d)(?=(\\s)*false)");
        Matcher matcher = pattern.matcher(queryResult);

        while (matcher.find()){
            indexes.add(Integer.parseInt(matcher.group()));

        }
        return indexes;
    }
}
