(* Draws figures/datum.pdf: the partial sum f_10 = sum_{k<=10} A_k Phi(./r_k) of the datum (2)
   of Part I, for the cutoff chi of the proof of Lemma 4.2 and the illustrative values
   A_1 = 1, mu = 17/16, sbar = a/16.
   Run: wolframscript -file figures/datum.wls *)
a0 = -7304210039150669*2^-54; d = 5764607523034235*2^-58;
xiL = -4528212286209965*2^-52; xia = -4077852323472915*2^-52;
xib = 1/2; xiR = 5404319552844595*2^-53;
aa = Exp[xiL - xiR];
H[x_] := 1/(1 + Exp[-2 x]);
e[x_] := If[x > 0, Exp[-1/x], 0];
S[x_] := If[x <= 0, 0, If[x >= 1, 1, e[x]/(e[x] + e[1 - x])]];
chi[xi_] := S[(xi - xiL)/(xia - xiL)] S[(xiR - xi)/(xiR - xib)];
P[xi_] := chi[xi] H[(xi - a0)/d] H[-xi/d];
(* Phi(y) = P(xiR + log|y|) *)
nR = 10; A1 = 1; mu = 17/16; sbar = aa/16;
A[k_] := A1 mu^(k - 1);
logr[k_] := Sum[Log[sbar] - j Log[2 mu], {j, 1, k - 1}];   (* log r_k, r_1 = 1 *)
lr = N[Table[logr[k], {k, 1, nR}]];
(* f_10 as a function of x = log10|y| *)
f[x_?NumericQ] := Sum[A[k] N[P[xiR + x Log[10] - lr[[k]]]], {k, 1, nR}];
xmin = (lr[[nR]] + N[Log[aa]])/Log[10] - 1.5; xmax = 0.3;
prof = Plot[f[x], {x, xmin, xmax}, PlotRange -> {{xmin, xmax}, {0, 1.05 N[mu^(nR - 1)]}},
   PlotPoints -> 6000, MaxRecursion -> 3, PlotStyle -> Directive[Black, Thickness[0.002]],
   Filling -> Axis, FillingStyle -> GrayLevel[0.35], Exclusions -> None,
   Frame -> True, FrameLabel -> {Row[{Subscript["log", 10], " |y|"}], Subscript["f", 10]},
   LabelStyle -> Directive[Black, 11], AspectRatio -> 0.55, ImageSize -> 330];
(* logarithmic polar picture: the point at angle theta and radius R in [0,1] shows f_10 at
   log|y| = (1 - R) lmin, so that all ten rings are visible *)
lmin = xmin Log[10];
n = 1201; L = 1.0;
(* each ring drawn with its own amplitude normalized to 1, so that all rings are visible *)
g[rr_] := If[rr > 1, 0, Sum[N[P[xiR + (1 - rr) lmin - lr[[k]]]], {k, 1, nR}]];
img = Image[Table[1 - g[Sqrt[x^2 + y^2]], {y, L, -L, -2 L/(n - 1)}, {x, -L, L, 2 L/(n - 1)}]];
dens = Graphics[{Inset[img, {0, 0}, Center, {2 L, 2 L}]}, PlotRange -> {{-L, L}, {-L, L}},
   Frame -> False, AspectRatio -> 1, ImageSize -> 190];
fig = GraphicsRow[{prof, dens}, Spacings -> 25, ImageSize -> 540];
Export[FileNameJoin[{DirectoryName[$InputFileName], "datum.pdf"}], fig];
Print["log10 r_k = ", lr/Log[10]];
Print["xmin = ", xmin, "  A_10 = ", N[A[nR]]];
