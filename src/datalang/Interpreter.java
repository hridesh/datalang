package datalang;
import java.io.IOException;

import datalang.Env;
import datalang.Value;
import datalang.AST.Program;
import datalang.AST.ProgramError;

/**
 * This main class implements the Read-Eval-Print-Loop of the interpreter with
 * the help of Reader, Evaluator, and Printer classes. 
 * 
 * @author hridesh
 *
 */
public class Interpreter {
	public static void main(String[] args) {
		System.out.println("DataLang: Type a program to evaluate and press the enter key,\n" + 
				"e.g. (define ev (event (a b)))  which creates an event\n" + 
                "     (when ev do (+ a b)) which creates an observer expression\n" + 
                "     (announce ev 2 3) which fires event ev \n" + 
				"then try (when ev do (* a b)) which creates another observer \n" +
				"then try (announce ev (2 3)) which fires event ev again (note the change).\n" +
				"Press Ctrl + C to exit.");
		Reader reader = new Reader();
		Evaluator eval = new Evaluator(reader);
		Printer printer = new Printer();
		REPL: while (true) { // Read-Eval-Print-Loop (also known as REPL)
			Program p = null;
			try {
				p = reader.read();
				if(p._e == null) continue REPL;
				Value val = eval.valueOf(p);
				printer.print(val);
			} catch (Env.LookupException e) {
				printer.print(e);
			} catch (IOException e) {
				System.out.println("Error reading input:" + e.getMessage());
			} catch (NullPointerException e) {
				System.out.println("Error: " + e.getMessage());
			} catch (ProgramError e) {
				System.out.println("Error: " + e.getMessage());
			}
		}
	}
}
