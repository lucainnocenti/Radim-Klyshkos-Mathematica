(* ::Package:: *)

BeginPackage["generalizedKlyshkoCriteria`"];

Unprotect @@ Names["generalizedKlyshkoCriteria`*"];
ClearAll @@ Names["generalizedKlyshkoCriteria`*"];
ClearAll @@ Names["generalizedKlyshkoCriteria`Private`*"];

klyshkoBasicCriteria;
klyshkoInfCriterion;
poisson;

Begin["`Private`"];


(* this is used when the probabilities are given as a list *)
klyshkoBasicCriteria[n_Integer, probs_List] /; (
    n > 0 && Length @ probs >= n + 1
) := (n! probs[[n+1]])^2 - (n-1)! (n+1)! probs[[n]] probs[[n+2]];
(* this is used when the probabilities are given as a function P[n] *)
klyshkoBasicCriteria[n_Integer, probsFun_ : Global`P] /; n > 0 := (
    (n! probsFun[n])^2 - (n-1)! (n+1)! probsFun[n-1] probsFun[n+1]
);


(* Generate the "K_infty" quantities *)
klyshkoInfCriterion[n_Integer, probs_List] := With[{
        expr = klyshkoInfCriterion[n, P]
    },
    expr /. P[m_] :> probs[[m + 1]]
];

klyshkoInfCriterion[n_Integer, probsFun_ : Global`P] /; n >= 2 := Module[{Q},
    Q[m_] := m! * probsFun[m];
    Plus[
        Sum[probsFun[k], {k, 0, n-2}],
        Q[n-1]^n / Q[n]^(n-1) * Plus[
            Exp[Q[n] / Q[n-1]]
            - Sum[(Q[n] / Q[n-1])^k / k!, {k, 0, n-2}]
        ] -1
    ]
];


(* Single Poisson probability distributions *)
poisson[lambda_, n_] := Exp[-lambda] lambda^n / n!;
(* Mixture of Poissonians *)
poisson[lambdas_List, weights_List, n_] /; Length @ lambdas == Length @ weights := Sum[
    Exp[-lambdas[[idx]]] lambdas[[idx]]^n weights[[idx]],
    {idx, Length @ lambdas}
] / n!;

(* Protect all package symbols *)
With[{syms = Names["generalizedKlyshkoCriteria`*"]},
  SetAttributes[syms, {Protected, ReadProtected}]
];

End[];
EndPackage[];
