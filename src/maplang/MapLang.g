grammar MapLang;
import RefLang; 
 
exp returns [Exp ast]: 
		va=varexp { $ast = $va.ast; }
		| num=numexp { $ast = $num.ast; }
		| str=strexp { $ast = $str.ast; }
		| bl=boolexp { $ast = $bl.ast; }
        | add=addexp { $ast = $add.ast; }
        | sub=subexp { $ast = $sub.ast; }
        | mul=multexp { $ast = $mul.ast; }
        | div=divexp { $ast = $div.ast; }
        | let=letexp { $ast = $let.ast; }
        | lam=lambdaexp { $ast = $lam.ast; }
        | call=callexp { $ast = $call.ast; }
        | i=ifexp { $ast = $i.ast; }
        | less=lessexp { $ast = $less.ast; }
        | eq=equalexp { $ast = $eq.ast; }
        | gt=greaterexp { $ast = $gt.ast; }
        | car=carexp { $ast = $car.ast; }
        | cdr=cdrexp { $ast = $cdr.ast; }
        | cons=consexp { $ast = $cons.ast; }
        | list=listexp { $ast = $list.ast; }
        | nl=nullexp { $ast = $nl.ast; }
        | lrec=letrecexp { $ast = $lrec.ast; }
        | ref=refexp { $ast = $ref.ast; }
        | deref=derefexp { $ast = $deref.ast; }
        | assign=assignexp { $ast = $assign.ast; }
        | free=freeexp { $ast = $free.ast; }
//TODO: | fork=forkexp { $ast = $fork.ast; }
//TODO: | lock=lockexp { $ast = $lock.ast; }
//TODO: | ulock=unlockexp { $ast = $ulock.ast; }
        ;
 
// forkexp returns [ForkExp ast] :
//        '(' Fork
//            e1=exp
//            e2=exp
//        ')' { $ast = new ForkExp($e1.ast, $e2.ast); }
//         ;
//
// lockexp returns [LockExp ast] :
//        '(' Lock
//            e1=exp
//        ')' { $ast = new LockExp($e1.ast); }
//         ;
//
// unlockexp returns [UnlockExp ast] :
//        '(' UnLock
//            e1=exp
//        ')' { $ast = new UnlockExp($e1.ast); }
//         ;
 