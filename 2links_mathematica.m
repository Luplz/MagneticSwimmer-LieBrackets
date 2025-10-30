e1 = {1,0,0};
e2 = {0, 1, 0};
e3 = {0, 0, 1};
x = Symbol["x"];
y = Symbol["y"];
z = Symbol["z"];
X = {x, y, z};
kel = Symbol["kel"];
m = Symbol["m"];  

(* Identity and zero matrices *)
Zero3x3 = ConstantArray[0, {3,3}];
Zero3x6 = ConstantArray[0, {3,6}];
Zero6x3 = ConstantArray[0, {6,3}];
Zero6x6 = ConstantArray[0, {6,6}];
Zero6x4 = ConstantArray[0, {6,4}];
Zero4x6 = ConstantArray[0, {4,6}];
Zero3x2 = ConstantArray[0, {3,2}];
Zero2x3 = ConstantArray[0, {2,3}];
Zero4x3 = ConstantArray[0, {4,3}];
Zero3x4 = ConstantArray[0, {3,4}];
Zero6 = ConstantArray[0, 6];  
Zero3 = ConstantArray[0, 3];  
Zero4 = ConstantArray[0, 4];  
I3 = IdentityMatrix[3];
I4 = IdentityMatrix[4];
I6 = IdentityMatrix[6];
I6x3 = ArrayFlatten[{{I3},{I3}}]; 
I6x6 = ArrayFlatten[{{I3, Zero3x3},{Zero3x3, I3}}];  


(* Define rotation matrices about x, y, z axes *)
Rx[tx_] := {{1,0,0},{0,Cos[tx],-Sin[tx]},{0,Sin[tx],Cos[tx]}};
Ry[ty_] := {{Cos[ty],0,Sin[ty]},{0,1,0},{-Sin[ty],0,Cos[ty]}};
Rz[tz_] := {{Cos[tz],-Sin[tz],0},{Sin[tz],Cos[tz],0},{0,0,1}};

(* Define skew matrices *)
Skew[v_] := {{0, -v[[3]], v[[2]]}, {v[[3]], 0, -v[[1]]}, {-v[[2]], v[[1]], 0}};

(* Define Rh *)
Rh = Simplify[Rx[tx].Ry[ty].Rz[tz]];

(* Define R1 and R2 *)
R1 = Simplify[Ry[phi1y].Rz[phi1z]];
R2 = Simplify[Ry[phi2y].Rz[phi2z]];

(* Define RhR1 and RhR2 *)
RhR1 = Simplify[Rh . R1];
RhR2 = Simplify[Rh . R2];

(* Define SkewRhR1e1 and SkewRhR2e1 *)
SkewRhR1e1 = Skew[RhR1.e1];
SkewRhR2e1 = Skew[RhR2.e1];

(* Define R1_proj and R2_proj *)
RhR1T = Transpose[RhR1];
RhR2T = Transpose[RhR2];
R1proj = Simplify[RhR1T[[{2, 3}, All]]];
R2proj = Simplify[RhR2T[[{2, 3}, All]]];

(* Define X1 and X2 *)
X1 = Simplify[X - r * Rh . e1];
X2 = Simplify[X1 - l * (Rh . R1 . e1)]; 

(* Define SkewX1X, SkewX2X, SkewX2X1 *)
SkewX1X = Simplify[Skew[X1 - X]];
SkewX2X = Simplify[Skew[X2 - X]];
SkewX2X1 = Simplify[Skew[X2 - X1]];

(* Define Dh *)
Dh = DiagonalMatrix[{khpara, khortho, khortho}];

(* Define D1 and D2 *)
D1 = DiagonalMatrix[{k1para, k1ortho, k1ortho}];
D2 = DiagonalMatrix[{k1para, k1ortho, k1ortho}];

(* Define D1tilde and D2tilde *)
D1tilde = Simplify[R1 . D1 . Transpose[R1]];
D2tilde = Simplify[R2 . D2 . Transpose[R2]];

(* Define RhD1tildeRhT and RhD2tildeRhT *)
RhD1tildeRhT = Rh . D1tilde . Transpose[Rh];
RhD2tildeRhT = Rh . D2tilde . Transpose[Rh];

(* Define Lh *)
Lh = {
  {1, 0, Sin[ty]},
  {0, Cos[tx], -Cos[ty]*Sin[tx]},
  {0, Sin[tx], Cos[tx]*Cos[ty]}
};

(* Define L1 and L2 *)
L1 = {
  {0, Sin[phi1y]},
  {1, 0},
  {0, Cos[phi1y]}
};

L2 = {
  {0, Sin[phi2y]},
  {1, 0},
  {0, Cos[phi2y]}
};


(* ====================== B matrix ================== *)
Print["Compute B matrix"]
(* B *)
B = ArrayFlatten[{
  {I3, Zero3x3, Zero3x2, Zero3x2},
  {Zero3x3, Lh, Zero3x2, Zero3x2},
  {Zero3x3, Zero3x3, L1, Zero3x2},
  {Zero3x3, Zero3x3, Zero3x2, L2}
}];

MatL = ArrayFlatten[{
  {L1, Zero3x2},
  {Zero3x2, L2}
}];


(* ===================== Q matrix ================== *)
Print["Compute Q matrix"]
(* qh *)
qhh = ConstantArray[0,{6,3}];
qhh[[1;;3,1;;3]] = r * Skew[Rh.e1];
qhh[[4;;6,1;;3]] = r * Skew[Rh.e1] + l * SkewRhR1e1;
qh = Simplify[qhh];

(* qL *)
qLL = ConstantArray[0,{6,6}];
qLL[[4;;6,1;;3]] = l * Rh.Skew[R1.e1];
qL = Simplify[qLL];

(* Q *)
Q = ArrayFlatten[{
  {I3, Zero3x3, Zero3x6},
  {I6x3, qh, qL},
  {Zero3x3, I3, Zero3x6},
  {Zero6x3, Zero6x3, I6x6}
}];


(* ===================== A matrix ================== *)
Print["Compute A matrix"]
(* AF_Xh *)
AFXh = -Rh . Dh . Transpose[Rh] * r;

(* AF_Omegah *)
AFOmegah = -(l^2/2) *
   (RhD1tildeRhT . SkewRhR1e1 +
    RhD2tildeRhT . SkewRhR2e1);

(* AT_Omegah *)
ATOmegah = -kr * r^3 * I3 + l^2 * (  (l/3 * SkewRhR1e1 - 1/2 * SkewX1X) . RhD1tildeRhT . SkewRhR1e1 + (l/3 * SkewRhR2e1 - 1/2 * SkewX2X) . RhD2tildeRhT . SkewRhR2e1);

(* AF_X *) 
AFX1 = -RhD1tildeRhT * l;
AFX2 = -RhD2tildeRhT * l;
AFX = ArrayFlatten[{{AFX1, AFX2}}];   

(* AF_Omega *)
AFOmega1 = - (l^2/2) * Rh . D1tilde . Skew[R1 . e1];
AFOmega2 = - (l^2/2) * Rh . D2tilde . Skew[R2 . e1];
AFOmega = ArrayFlatten[{{AFOmega1, AFOmega2}}];

(* AT_X *)
ATX1 = l * (l/2 * SkewRhR1e1 - SkewX1X) . RhD1tildeRhT;
ATX2 = l * (l/2 * SkewRhR2e1 - SkewX2X) . RhD2tildeRhT;
ATX =  ArrayFlatten[{{ATX1, ATX2}}];

(* AT_Omega *)
ATOmega1 = l^2 * (l/3 * SkewRhR1e1 - 1/2 * SkewX1X) . Rh . D1tilde . Skew[R1 . e1];
ATOmega2 = l^2 * (l/3 * SkewRhR2e1 - 1/2 * SkewX2X) . Rh . D2tilde . Skew[R2 . e1];
ATOmega = ArrayFlatten[{{ATOmega1, ATOmega2}}];

(* ATlink_X *)
ATlinkX11 = l * R1proj . (l/2 * SkewRhR1e1) . RhD1tildeRhT;
ATlinkX12 = l * R1proj . (l/2 * SkewRhR2e1 - SkewX2X1) . RhD2tildeRhT;

ATlinkX21 = Zero2x3;
ATlinkX22 = l * R2proj . (l/2 * SkewRhR2e1) . RhD2tildeRhT;

ATlinkX = ArrayFlatten[{
  {ATlinkX11, ATlinkX12},
  {ATlinkX21, ATlinkX22}
}];

(* ATlink_Omega *)
ATlinkOmega11 = l^2 * R1proj . (l/3 * SkewRhR1e1) . Rh . D1tilde . Skew[R1 . e1];
ATlinkOmega12 = l^2 * R1proj . (l/3 * SkewRhR2e1 -  1/2 * SkewX2X1) . Rh . D2tilde . Skew[R2 . e1];

ATlinkOmega21 = Zero2x3;
ATlinkOmega22 = l^2 * R2proj . (l/3 * SkewRhR2e1) . Rh . D2tilde . Skew[R2 . e1];

ATlinkOmega = ArrayFlatten[{
  {ATlinkOmega11, ATlinkOmega12},
  {ATlinkOmega21, ATlinkOmega22}
}];

(* A *)
A = ArrayFlatten[{
  {AFXh, AFX, AFOmegah, AFOmega},
  {Zero3x3, ATX, ATOmegah, ATOmega},
  {Zero4x3, ATlinkX, Zero4x3, ATlinkOmega}
}];


(* ===================== Mass matrix in PLANAR case ================== *)
Print["Compute Mass matrix and inverse in planar case"]

(* We set tx=ty=phi1y=phi2y=0 for planar motion in plan z=0 *)
tx = 0;
ty = 0;
phi1y = 0;
phi2y = 0;


(* Mass matrix and inverse *)
MassMat = Simplify[A.Q.B];
MassMatInv = Inverse[MassMat];

(* Determinant *)
indices = {1, 2, 6, 8, 10};
MassMatplan = MassMat[[indices, indices]];
Determinant = Simplify[Det[MassMatplan]];
Print["Det =", Determinant];
DeterminantExpansion = Series[Determinant, {phi1z, 0, 0}, {phi2z, 0, 0}, {tz, 0, 0}];
DeterminantExpansion = Simplify[DeterminantExpansion];
Print["DetExpansion =", DeterminantExpansion];



(* ==================== Vector fields ========================= *)
Print["Compute vector fields"]
F01 = R1proj . Skew[Rh . R1 . e1] . (Rh . e1);
F02 = R2proj . Skew[Rh . R2 . e1] . (Rh . R1 . e1);  
F00 = Simplify[kel * Join[Zero6, F01, F02]];

F11 = Simplify[m * Join[Zero3,  Skew[Rh . e1] . e1, Zero4]];
F22 = Simplify[m * Join[Zero3,  Skew[Rh . e1] . e2, Zero4]];
F33 = Simplify[m * Join[Zero3,  Skew[Rh . e1] . e3, Zero4]];


(* LHS *)
Print["LHS"];
F0 = MassMatInv . F00;
F1 = MassMatInv . F11;
F2 = MassMatInv . F22;
F3 = MassMatInv . F33;

(* keep only usefull components, i.e x,y,tz,phi1z,phi2z *)
indices = {1, 2, 6, 8, 10};


FF0 = Simplify[F0[[indices]]];
FF1 = Simplify[F1[[indices]]];
FF2 = Simplify[F2[[indices]]];
FF3 = Simplify[F3[[indices]]];

(* Transform FF0, FF1 and FF2 in functions *)
Print["FF0, FF1 and FF2 in functions"];
FF0fun[xx_, yy_, tzz_, phi1zz_, phi2zz_] :=
  FF0 /. {x -> xx, y -> yy, tz -> tzz, phi1z -> phi1zz, phi2z -> phi2zz};

FF1fun[xx_, yy_, tzz_, phi1zz_, phi2zz_] :=
  FF1 /. {x -> xx, y -> yy, tz -> tzz, phi1z -> phi1zz, phi2z -> phi2zz};

FF2fun[xx_, yy_, tzz_, phi1zz_, phi2zz_] :=
  FF2 /. {x -> xx, y -> yy, tz -> tzz, phi1z -> phi1zz, phi2z -> phi2zz};




(* ======================= Lie Brackets ========================== *)

(* Lie bracket function *)
LieBrack[dxf_, dyf_, dtzf_, dphi1f_, dphi2f_, f_,
          dxg_, dyg_, dtzg_, dphi1g_, dphi2g_, g_][xx_, yy_, tz_, phi1z_, phi2z_] :=
  Module[{fval, gval, Df, Dg},
   
   (* Evaluate f and g at the point *)
   fval = f[xx, yy, tz, phi1z, phi2z];
   gval = g[xx, yy, tz, phi1z, phi2z];
   
   (* Build Jacobians by stacking partial derivatives as rows *)
   Df = {
     dxf[xx, yy, tz, phi1z, phi2z],
     dyf[xx, yy, tz, phi1z, phi2z],
     dtzf[xx, yy, tz, phi1z, phi2z],
     dphi1f[xx, yy, tz, phi1z, phi2z],
     dphi2f[xx, yy, tz, phi1z, phi2z]
   };
   
   Dg = {
     dxg[xx, yy, tz, phi1z, phi2z],
     dyg[xx, yy, tz, phi1z, phi2z],
     dtzg[xx, yy, tz, phi1z, phi2z],
     dphi1g[xx, yy, tz, phi1z, phi2z],
     dphi2g[xx, yy, tz, phi1z, phi2z]
   };
   
   (* Lie bracket: Dg.f - Df.g *)
   Transpose[Dg].fval - Transpose[Df].gval
]


(* Lie brackets of order 2 *)
dxF0[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF0fun[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF0[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF0fun[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF0[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF0fun[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F0[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF0fun[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F0[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF0fun[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};


dxF1[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF1fun[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF1[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF1fun[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF1[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF1fun[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F1[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF1fun[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F1[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF1fun[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};


dxF2[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF2fun[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF2[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF2fun[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF2[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF2fun[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F2[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF2fun[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F2[xx_, yy_, tz_, phi1z_, phi2z_] := D[FF2fun[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
 

F01 = LieBrack[dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun,           
     dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun]; 

F10 = LieBrack[dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun,           
     dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun]; 

F02 = LieBrack[dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun,           
     dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun]; 

F20 = LieBrack[dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun,           
     dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun]; 

F12 = LieBrack[dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun,           
     dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun]; 

F21 = LieBrack[dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun,           
     dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun]; 


(* Lie brackets of order 3 *)
dxF01[xx_, yy_, tz_, phi1z_, phi2z_] := D[F01[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF01[xx_, yy_, tz_, phi1z_, phi2z_] := D[F01[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF01[xx_, yy_, tz_, phi1z_, phi2z_] := D[F01[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F01[xx_, yy_, tz_, phi1z_, phi2z_] := D[F01[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F01[xx_, yy_, tz_, phi1z_, phi2z_] := D[F01[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};


dxF02[xx_, yy_, tz_, phi1z_, phi2z_] := D[F02[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF02[xx_, yy_, tz_, phi1z_, phi2z_] := D[F02[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF02[xx_, yy_, tz_, phi1z_, phi2z_] := D[F02[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F02[xx_, yy_, tz_, phi1z_, phi2z_] := D[F02[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F02[xx_, yy_, tz_, phi1z_, phi2z_] := D[F02[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};


dxF12[xx_, yy_, tz_, phi1z_, phi2z_] := D[F12[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF12[xx_, yy_, tz_, phi1z_, phi2z_] := D[F12[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF12[xx_, yy_, tz_, phi1z_, phi2z_] := D[F12[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F12[xx_, yy_, tz_, phi1z_, phi2z_] := D[F12[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F12[xx_, yy_, tz_, phi1z_, phi2z_] := D[F12[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};

F202 = LieBrack[dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun,           
     dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02]; 

F212 = LieBrack[dxF2, dyF2, dtzF2, dphi1F2, dphi2F2, FF2fun,           
     dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12]; 


F002 = LieBrack[dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun,           
     dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02]; 

F102 = LieBrack[dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun,           
     dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02]; 

F012 = LieBrack[dxF0, dyF0, dtzF0, dphi1F0, dphi2F0, FF0fun,           
     dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12]; 

F112 = LieBrack[dxF1, dyF1, dtzF1, dphi1F1, dphi2F1, FF1fun,           
     dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12]; 

(* Lie brackets of order 4 and 5 *)
dxF002[xx_, yy_, tz_, phi1z_, phi2z_] := D[F002[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF002[xx_, yy_, tz_, phi1z_, phi2z_] := D[F002[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF002[xx_, yy_, tz_, phi1z_, phi2z_] := D[F002[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F002[xx_, yy_, tz_, phi1z_, phi2z_] := D[F002[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F002[xx_, yy_, tz_, phi1z_, phi2z_] := D[F002[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};

dxF102[xx_, yy_, tz_, phi1z_, phi2z_] := D[F102[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF102[xx_, yy_, tz_, phi1z_, phi2z_] := D[F102[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF102[xx_, yy_, tz_, phi1z_, phi2z_] := D[F102[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F102[xx_, yy_, tz_, phi1z_, phi2z_] := D[F102[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F102[xx_, yy_, tz_, phi1z_, phi2z_] := D[F102[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};

dxF012[xx_, yy_, tz_, phi1z_, phi2z_] := D[F012[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF012[xx_, yy_, tz_, phi1z_, phi2z_] := D[F012[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF012[xx_, yy_, tz_, phi1z_, phi2z_] := D[F012[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F012[xx_, yy_, tz_, phi1z_, phi2z_] := D[F012[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F012[xx_, yy_, tz_, phi1z_, phi2z_] := D[F012[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};

dxF112[xx_, yy_, tz_, phi1z_, phi2z_] := D[F112[u,v,w,s,t], u] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dyF112[xx_, yy_, tz_, phi1z_, phi2z_] := D[F112[u,v,w,s,t], v] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dtzF112[xx_, yy_, tz_, phi1z_, phi2z_] := D[F112[u,v,w,s,t], w] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi1F112[xx_, yy_, tz_, phi1z_, phi2z_] := D[F112[u,v,w,s,t], s] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};
dphi2F112[xx_, yy_, tz_, phi1z_, phi2z_] := D[F112[u,v,w,s,t], t] /. {u -> xx, v -> yy, w -> tz, s -> phi1z, t -> phi2z};


F1202 = LieBrack[dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12,           
     dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02]; 


F02002 = LieBrack[dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02,           
     dxF002, dyF002, dtzF002, dphi1F002, dphi2F002, F002]; 

F02102 = LieBrack[dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02,           
     dxF102, dyF102, dtzF102, dphi1F102, dphi2F102, F102]; 

F12012 = LieBrack[dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12,           
     dxF012, dyF012, dtzF012, dphi1F012, dphi2F012, F012]; 

F12112 = LieBrack[dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12,           
     dxF112, dyF112, dtzF112, dphi1F112, dphi2F112, F112]; 

F12002 = LieBrack[dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12,           
     dxF002, dyF002, dtzF002, dphi1F002, dphi2F002, F002]; 


F02012 = LieBrack[dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02,           
     dxF012, dyF012, dtzF012, dphi1F012, dphi2F012, F012]; 

F12102 = LieBrack[dxF12, dyF12, dtzF12, dphi1F12, dphi2F12, F12,           
     dxF102, dyF102, dtzF102, dphi1F102, dphi2F102, F102]; 

F02112 = LieBrack[dxF02, dyF02, dtzF02, dphi1F02, dphi2F02, F02,           
     dxF112, dyF112, dtzF112, dphi1F112, dphi2F112, F112]; 

(* ========================== ASSUMTIONS ================================== *)
F0in0 = Simplify[FF0fun[0,0,0,0,0]];
F1in0 = Simplify[FF1fun[0,0,0,0,0]];
F2in0 = Simplify[FF2fun[0,0,0,0,0]];

dxF01in0 = Simplify[dxF0[0,0,0,0,0][[1]]];
dyF01in0 = Simplify[dyF0[0,0,0,0,0][[1]]];
dtzF01in0 = Simplify[dtzF0[0,0,0,0,0][[1]]];
dphi1F01in0 = Simplify[dphi1F0[0,0,0,0,0][[1]]];
dphi2F01in0 = Simplify[dphi2F0[0,0,0,0,0][[1]]];

dxF11in0 = Simplify[dxF1[0,0,0,0,0][[1]]];
dyF11in0 = Simplify[dyF1[0,0,0,0,0][[1]]];
dtzF11in0 = Simplify[dtzF1[0,0,0,0,0][[1]]];
dphi1F11in0 = Simplify[dphi1F1[0,0,0,0,0][[1]]];
dphi2F11in0 = Simplify[dphi2F1[0,0,0,0,0][[1]]];


(* Assumptions *)
Print["================== ASSUMPTIONS ==================="];
Print["F0(0)=0 :", F0in0];
Print["F1(0)=0 :", F1in0];
Print["F2^(1)(0)=0 :", F2in0];

Print["nabla F0^(1) :", {dxF01in0, dyF01in0, dtzF01in0, dphi1F01in0, dphi2F01in0}];
Print["nabla F1^(1) :", {dxF11in0, dyF11in0, dtzF11in0, dphi1F11in0, dphi2F11in0}];


(* =========================== CASE 1 ===================================== *)
Print["=================== CASE 1 ======================="]
F202in0 = Simplify[F202[0,0,0,0,0]];
F212in0 = Simplify[F212[0,0,0,0,0]];

Print["F212(0)=0 :", F212in0];
Print["F202(0)=a x e_1 :", F202in0];


(* =========================== CASE 2 ===================================== *)
Print["=================== CASE 2 ======================="]
(* The first component of F202in0 vanishes *)
constraint = (F202in0[[1]] == 0);

F212in0 = F212[0,0,0,0,0];
F1202in0 = F1202[0,0,0,0,0];
F202in0 = FullSimplify[F202in0, constraint];
F212in0 = FullSimplify[F212in0, constraint];
F1202in0 = FullSimplify[F1202in0, constraint];

(* Assumptions *)
Print["F202(0) = 0 :", F202in0];
Print["F212(0) = 0 :", F212in0];
Print["F1202(0) = 0 :", F1202in0];

(* R' space *)
F02102in0 = FullSimplify[F02102[0,0,0,0,0], constraint];
F12112in0 = FullSimplify[F12112[0,0,0,0,0], constraint];
F12102in0 = FullSimplify[F12102[0,0,0,0,0], constraint];
F02112in0 = FullSimplify[F02112[0,0,0,0,0], constraint];
Rprime = F02102in0 + F12112in0 + F12102in0 + F02112in0;
Print["R' =", Rprime];

(* Du1eq map *)
F02002in0 = FullSimplify[F02002[0,0,0,0,0], constraint];
F02102in0 = FullSimplify[F02102[0,0,0,0,0], constraint];
F12012in0 = FullSimplify[F12012[0,0,0,0,0], constraint];
F12112in0 = FullSimplify[F12112[0,0,0,0,0], constraint];
F12002in0 = FullSimplify[F12002[0,0,0,0,0], constraint];
F02012in0 = FullSimplify[F02012[0,0,0,0,0], constraint];
F12102in0 = FullSimplify[F12102[0,0,0,0,0], constraint];
F02112in0 = FullSimplify[F02112[0,0,0,0,0], constraint];

D1ueq[lamb1_, lamb2_, u1eq_] := lamb1^2 * (F02002in0 - u1eq * F02102in0) + lamb2^2 * (F12012in0 - u1eq * F12112in0 ) - lamb1*lamb2 * (F12002in0 + F02012in0 - u1eq * (F12102in0 + F02112in0 ));   
Print["Du1eq = ", D1ueq[lamb1, lamb2, u1eq]];


  
