(* Draws figures/ring.pdf: the Ring of Definition 4.1 of Part I, for the cutoff chi of the proof of Lemma 4.2.
   Run: wolframscript -file figures/ring.wls *)
a0 = -7304210039150669*2^-54; d = 5764607523034235*2^-58;
xiL = -4528212286209965*2^-52; xia = -4077852323472915*2^-52;
xib = 1/2; xiR = 5404319552844595*2^-53;
Rc = Exp[xiR]; aa = Exp[xiL - xiR];
H[x_] := 1/(1 + Exp[-2 x]);
e[x_] := If[x > 0, Exp[-1/x], 0];
S[x_] := If[x <= 0, 0, If[x >= 1, 1, e[x]/(e[x] + e[1 - x])]];
chi[xi_] := S[(xi - xiL)/(xia - xiL)] S[(xiR - xi)/(xiR - xib)];
P[xi_] := chi[xi] H[(xi - a0)/d] H[-xi/d];
Phi[r_?NumericQ] := If[r <= 0, 0, N[P[Log[Rc r]]]];
prof = Plot[Phi[r], {r, 0, 1.08}, PlotRange -> {{0, 1.08}, {0, 1.05}}, PlotPoints -> 400,
   MaxRecursion -> 4, PlotStyle -> Directive[Black, Thickness[0.006]],
   Frame -> True, FrameLabel -> {"|y|", "\[CapitalPhi]"}, LabelStyle -> Directive[Black, 11],
   FrameTicks -> {{{0, 0.5, 1}, None}, {{0, 0.5, 1}, None}},
   GridLines -> {{N[aa], 1}, None}, GridLinesStyle -> Directive[Gray, Dashed],
   AspectRatio -> 0.8, ImageSize -> 260];
n = 401; L = 1.08;
img = Image[Table[1 - Phi[Sqrt[x^2 + y^2]], {y, L, -L, -2 L/(n - 1)}, {x, -L, L, 2 L/(n - 1)}]];
dens = Graphics[{Inset[img, {0, 0}, Center, {2 L, 2 L}]}, PlotRange -> {{-L, L}, {-L, L}},
   Frame -> True, FrameLabel -> {"\!\(\*SubscriptBox[\(y\), \(1\)]\)", "\!\(\*SubscriptBox[\(y\), \(2\)]\)"},
   LabelStyle -> Directive[Black, 11], FrameTicks -> {{{-1, 0, 1}, None}, {{-1, 0, 1}, None}},
   AspectRatio -> 1, ImageSize -> 220];
fig = GraphicsRow[{prof, dens}, Spacings -> 30, ImageSize -> 520];
Export[FileNameJoin[{DirectoryName[$InputFileName], "ring.pdf"}], fig];
Print["max Phi = ", NMaxValue[{Phi[r], 0.2 < r < 1}, r], "  plateau r range: ", N[Exp[a0]/Rc], " .. ", N[1/Rc]];
