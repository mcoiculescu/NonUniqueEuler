(* Prints the constants of Definition 4.1 of Part I to 4 significant figures. *)
a0 = -7304210039150669*2^-54;
d = 5764607523034235*2^-58;
xiL = -4528212286209965*2^-52;
xia = -4077852323472915*2^-52;
xib = 1/2;
xiR = 5404319552844595*2^-53;
Rc = Exp[xiR]; a = Exp[xiL - xiR]; G1 = 1/50*Rc^-2;
vals = {"a0" -> a0, "d" -> d, "xiL" -> xiL, "xia" -> xia, "xiR" -> xiR, "Rc" -> Rc, "a" -> a, "G1" -> G1};
Do[Print[v[[1]], "  ", N[v[[2]], 12], "  ->  ", NumberForm[N[v[[2]], 20], 4]], {v, vals}];
