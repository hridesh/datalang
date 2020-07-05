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
				"e.g. (job ((a (output (0 v) (+ result v)))) (seq (<< a 300) (<< a 40) (<< a 2)))\n" +
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
