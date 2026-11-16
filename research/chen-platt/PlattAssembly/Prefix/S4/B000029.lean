import PlattAssemblyKernel
import PlattCertificates.Count131072.C030928
import PlattCertificates.Count131072.C030929
import PlattCertificates.Count131072.C030930
import PlattCertificates.Count131072.C030931
import PlattCertificates.Count131072.C030932
import PlattCertificates.Count131072.C030933
import PlattCertificates.Count131072.C030934
import PlattCertificates.Count131072.C030935
import PlattCertificates.Count131072.C030936
import PlattCertificates.Count131072.C030937
import PlattCertificates.Count131072.C030938
import PlattCertificates.Count131072.C030939
import PlattCertificates.Count131072.C030940
import PlattCertificates.Count131072.C030941
import PlattCertificates.Count131072.C030942
import PlattCertificates.Count131072.C030943
import PlattCertificates.Count131072.C030944
import PlattCertificates.Count131072.C030945
import PlattCertificates.Count131072.C030946
import PlattCertificates.Count131072.C030947
import PlattCertificates.Count131072.C030948
import PlattCertificates.Count131072.C030949
import PlattCertificates.Count131072.C030950
import PlattCertificates.Count131072.C030951
import PlattCertificates.Count131072.C030952
import PlattCertificates.Count131072.C030953
import PlattCertificates.Count131072.C030954
import PlattCertificates.Count131072.C030955
import PlattCertificates.Count131072.C030956
import PlattCertificates.Count131072.C030957
import PlattCertificates.Count131072.C030958
import PlattCertificates.Count131072.C030959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30928 : List PrefixCut := [⟨15,50638272,50638301⟩,
⟨128,410788519,410788753⟩]
theorem checked30928 : checkPrefixCuts (2^48) 4057726977 9 Manual.Count131072.C030928.packed 128 cuts30928 = true := by
 decide +kernel
def pointBounds30928 : List (Nat × Nat × Nat) := [(4057742336,105615462619417,105615846158524)]
theorem point_links_checked30928 : (cuts30928.take 1).map (fun c => (4057726977-1+2*2^9*c.k,105615411981145+c.lower,105615795520223+c.upper)) = pointBounds30928 := by
 decide +kernel
def cuts30929 : List PrefixCut := [⟨11,34335817,34335837⟩,
⟨128,409596021,409596254⟩]
theorem checked30929 : checkPrefixCuts (2^48) 4057858049 9 Manual.Count131072.C030929.packed 128 cuts30929 = true := by
 decide +kernel
def pointBounds30929 : List (Nat × Nat × Nat) := [(4057869312,105615857105481,105616240644813)]
theorem point_links_checked30929 : (cuts30929.take 1).map (fun c => (4057858049-1+2*2^9*c.k,105615822769664+c.lower,105616206308976+c.upper)) = pointBounds30929 := by
 decide +kernel
def cuts30930 : List PrefixCut := [⟨7,22751092,22751104⟩,
⟨128,410068343,410068570⟩]
theorem checked30930 : checkPrefixCuts (2^48) 4057989121 9 Manual.Count131072.C030930.packed 128 cuts30930 = true := by
 decide +kernel
def pointBounds30930 : List (Nat × Nat × Nat) := [(4057996288,105616255116777,105616638656334)]
theorem point_links_checked30930 : (cuts30930.take 1).map (fun c => (4057989121-1+2*2^9*c.k,105616232365685+c.lower,105616615905230+c.upper)) = pointBounds30930 := by
 decide +kernel
def cuts30931 : List PrefixCut := [⟨3,9710523,9710529⟩,
⟨127,406101646,406101877⟩,
⟨128,409708297,409708530⟩]
theorem checked30931 : checkPrefixCuts (2^48) 4058120193 9 Manual.Count131072.C030931.packed 128 cuts30931 = true := by
 decide +kernel
def pointBounds30931 : List (Nat × Nat × Nat) := [(4058123264,105616652144551,105617035684329),(4058250240,105617048535674,105617432075677)]
theorem point_links_checked30931 : (cuts30931.take 2).map (fun c => (4058120193-1+2*2^9*c.k,105616642434028+c.lower,105617025973800+c.upper)) = pointBounds30931 := by
 decide +kernel
def cuts30932 : List PrefixCut := [⟨123,398043196,398043421⟩,
⟨128,413787114,413787349⟩]
theorem checked30932 : checkPrefixCuts (2^48) 4058251265 9 Manual.Count131072.C030932.packed 128 cuts30932 = true := by
 decide +kernel
def pointBounds30932 : List (Nat × Nat × Nat) := [(4058377216,105617450185521,105617833725751)]
theorem point_links_checked30932 : (cuts30932.take 1).map (fun c => (4058251265-1+2*2^9*c.k,105617052142325+c.lower,105617435682330+c.upper)) = pointBounds30932 := by
 decide +kernel
def cuts30933 : List PrefixCut := [⟨119,383119082,383119303⟩,
⟨128,410791432,410791670⟩]
theorem checked30933 : checkPrefixCuts (2^48) 4058382337 9 Manual.Count131072.C030933.packed 128 cuts30933 = true := by
 decide +kernel
def pointBounds30933 : List (Nat × Nat × Nat) := [(4058504192,105617849048521,105618232588982)]
theorem point_links_checked30933 : (cuts30933.take 1).map (fun c => (4058382337-1+2*2^9*c.k,105617465929439+c.lower,105617849469679+c.upper)) = pointBounds30933 := by
 decide +kernel
def cuts30934 : List PrefixCut := [⟨115,367987951,367988159⟩,
⟨128,411610397,411610629⟩]
theorem checked30934 : checkPrefixCuts (2^48) 4058513409 9 Manual.Count131072.C030934.packed 128 cuts30934 = true := by
 decide +kernel
def pointBounds30934 : List (Nat × Nat × Nat) := [(4058631168,105618244708822,105618628249508)]
theorem point_links_checked30934 : (cuts30934.take 1).map (fun c => (4058513409-1+2*2^9*c.k,105617876720871+c.lower,105618260261349+c.upper)) = pointBounds30934 := by
 decide +kernel
def cuts30935 : List PrefixCut := [⟨111,355839894,355840093⟩,
⟨128,411181078,411181308⟩]
theorem checked30935 : checkPrefixCuts (2^48) 4058644481 9 Manual.Count131072.C030935.packed 128 cuts30935 = true := by
 decide +kernel
def pointBounds30935 : List (Nat × Nat × Nat) := [(4058758144,105618644171162,105619027712071)]
theorem point_links_checked30935 : (cuts30935.take 1).map (fun c => (4058644481-1+2*2^9*c.k,105618288331268+c.lower,105618671871978+c.upper)) = pointBounds30935 := by
 decide +kernel
def cuts30936 : List PrefixCut := [⟨107,343692467,343692662⟩,
⟨128,410335555,410335786⟩]
theorem checked30936 : checkPrefixCuts (2^48) 4058775553 9 Manual.Count131072.C030936.packed 128 cuts30936 = true := by
 decide +kernel
def pointBounds30936 : List (Nat × Nat × Nat) := [(4058885120,105619043204813,105619426745948)]
theorem point_links_checked30936 : (cuts30936.take 1).map (fun c => (4058775553-1+2*2^9*c.k,105618699512346+c.lower,105619083053286+c.upper)) = pointBounds30936 := by
 decide +kernel
def cuts30937 : List PrefixCut := [⟨103,329396223,329396410⟩,
⟨128,408796763,408796997⟩]
theorem checked30937 : checkPrefixCuts (2^48) 4058906625 9 Manual.Count131072.C030937.packed 128 cuts30937 = true := by
 decide +kernel
def pointBounds30937 : List (Nat × Nat × Nat) := [(4059012096,105619439244124,105619822785482)]
theorem point_links_checked30937 : (cuts30937.take 1).map (fun c => (4058906625-1+2*2^9*c.k,105619109847901+c.lower,105619493389072+c.upper)) = pointBounds30937 := by
 decide +kernel
def cuts30938 : List PrefixCut := [⟨99,317527872,317528053⟩,
⟨128,410933212,410933450⟩]
theorem checked30938 : checkPrefixCuts (2^48) 4059037697 9 Manual.Count131072.C030938.packed 128 cuts30938 = true := by
 decide +kernel
def pointBounds30938 : List (Nat × Nat × Nat) := [(4059139072,105619836172536,105620219714122)]
theorem point_links_checked30938 : (cuts30938.take 1).map (fun c => (4059037697-1+2*2^9*c.k,105619518644664+c.lower,105619902186069+c.upper)) = pointBounds30938 := by
 decide +kernel
def cuts30939 : List PrefixCut := [⟨95,308295214,308295389⟩,
⟨128,419032849,419033084⟩]
theorem checked30939 : checkPrefixCuts (2^48) 4059168769 9 Manual.Count131072.C030939.packed 128 cuts30939 = true := by
 decide +kernel
def pointBounds30939 : List (Nat × Nat × Nat) := [(4059266048,105620237873090,105620621414908)]
theorem point_links_checked30939 : (cuts30939.take 1).map (fun c => (4059168769-1+2*2^9*c.k,105619929577876+c.lower,105620313119519+c.upper)) = pointBounds30939 := by
 decide +kernel
def cuts30940 : List PrefixCut := [⟨91,294070754,294070917⟩,
⟨128,407855771,407856000⟩]
theorem checked30940 : checkPrefixCuts (2^48) 4059299841 9 Manual.Count131072.C030940.packed 128 cuts30940 = true := by
 decide +kernel
def pointBounds30940 : List (Nat × Nat × Nat) := [(4059393024,105620642681479,105621026223520)]
theorem point_links_checked30940 : (cuts30940.take 1).map (fun c => (4059299841-1+2*2^9*c.k,105620348610725+c.lower,105620732152603+c.upper)) = pointBounds30940 := by
 decide +kernel
def cuts30941 : List PrefixCut := [⟨87,279292437,279292601⟩,
⟨128,408882597,408882838⟩]
theorem checked30941 : checkPrefixCuts (2^48) 4059430913 9 Manual.Count131072.C030941.packed 128 cuts30941 = true := by
 decide +kernel
def pointBounds30941 : List (Nat × Nat × Nat) := [(4059520000,105621035758933,105621419301204)]
theorem point_links_checked30941 : (cuts30941.take 1).map (fun c => (4059430913-1+2*2^9*c.k,105620756466496+c.lower,105621140008603+c.upper)) = pointBounds30941 := by
 decide +kernel
def cuts30942 : List PrefixCut := [⟨83,265347146,265347293⟩,
⟨128,409424088,409424311⟩]
theorem checked30942 : checkPrefixCuts (2^48) 4059561985 9 Manual.Count131072.C030942.packed 128 cuts30942 = true := by
 decide +kernel
def pointBounds30942 : List (Nat × Nat × Nat) := [(4059646976,105621430696239,105621814238734)]
theorem point_links_checked30942 : (cuts30942.take 1).map (fun c => (4059561985-1+2*2^9*c.k,105621165349093+c.lower,105621548891441+c.upper)) = pointBounds30942 := by
 decide +kernel
def cuts30943 : List PrefixCut := [⟨79,256186715,256186861⟩,
⟨128,416552136,416552375⟩]
theorem checked30943 : checkPrefixCuts (2^48) 4059693057 9 Manual.Count131072.C030943.packed 128 cuts30943 = true := by
 decide +kernel
def pointBounds30943 : List (Nat × Nat × Nat) := [(4059773952,105621830959896,105622214502613)]
theorem point_links_checked30943 : (cuts30943.take 1).map (fun c => (4059693057-1+2*2^9*c.k,105621574773181+c.lower,105621958315752+c.upper)) = pointBounds30943 := by
 decide +kernel
def cuts30944 : List PrefixCut := [⟨75,241341713,241341852⟩,
⟨128,415290726,415290966⟩]
theorem checked30944 : checkPrefixCuts (2^48) 4059824129 9 Manual.Count131072.C030944.packed 128 cuts30944 = true := by
 decide +kernel
def pointBounds30944 : List (Nat × Nat × Nat) := [(4059900928,105622232667030,105622616209979)]
theorem point_links_checked30944 : (cuts30944.take 1).map (fun c => (4059824129-1+2*2^9*c.k,105621991325317+c.lower,105622374868127+c.upper)) = pointBounds30944 := by
 decide +kernel
def cuts30945 : List PrefixCut := [⟨71,226497630,226497757⟩,
⟨128,407165897,407166127⟩]
theorem checked30945 : checkPrefixCuts (2^48) 4059955201 9 Manual.Count131072.C030945.packed 128 cuts30945 = true := by
 decide +kernel
def pointBounds30945 : List (Nat × Nat × Nat) := [(4060027904,105622633113673,105623016656850)]
theorem point_links_checked30945 : (cuts30945.take 1).map (fun c => (4059955201-1+2*2^9*c.k,105622406616043+c.lower,105622790159093+c.upper)) = pointBounds30945 := by
 decide +kernel
def cuts30946 : List PrefixCut := [⟨67,212209117,212209238⟩,
⟨128,409371181,409371409⟩]
theorem checked30946 : checkPrefixCuts (2^48) 4060086273 9 Manual.Count131072.C030946.packed 128 cuts30946 = true := by
 decide +kernel
def pointBounds30946 : List (Nat × Nat × Nat) := [(4060154880,105623025991057,105623409534458)]
theorem point_links_checked30946 : (cuts30946.take 1).map (fun c => (4060086273-1+2*2^9*c.k,105622813781940+c.lower,105623197325220+c.upper)) = pointBounds30946 := by
 decide +kernel
def cuts30947 : List PrefixCut := [⟨63,201942341,201942459⟩,
⟨128,411229731,411229968⟩]
theorem checked30947 : checkPrefixCuts (2^48) 4060217345 9 Manual.Count131072.C030947.packed 128 cuts30947 = true := by
 decide +kernel
def pointBounds30947 : List (Nat × Nat × Nat) := [(4060281856,105623425095462,105623808639088)]
theorem point_links_checked30947 : (cuts30947.take 1).map (fun c => (4060217345-1+2*2^9*c.k,105623223153121+c.lower,105623606696629+c.upper)) = pointBounds30947 := by
 decide +kernel
def cuts30948 : List PrefixCut := [⟨59,190636398,190636504⟩,
⟨128,411355137,411355366⟩]
theorem checked30948 : checkPrefixCuts (2^48) 4060348417 9 Manual.Count131072.C030948.packed 128 cuts30948 = true := by
 decide +kernel
def pointBounds30948 : List (Nat × Nat × Nat) := [(4060408832,105623825019250,105624208563101)]
theorem point_links_checked30948 : (cuts30948.take 1).map (fun c => (4060348417-1+2*2^9*c.k,105623634382852+c.lower,105624017926597+c.upper)) = pointBounds30948 := by
 decide +kernel
def cuts30949 : List PrefixCut := [⟨55,174201445,174201547⟩,
⟨128,410579252,410579486⟩]
theorem checked30949 : checkPrefixCuts (2^48) 4060479489 9 Manual.Count131072.C030949.packed 128 cuts30949 = true := by
 decide +kernel
def pointBounds30949 : List (Nat × Nat × Nat) := [(4060535808,105624219939434,105624603483510)]
theorem point_links_checked30949 : (cuts30949.take 1).map (fun c => (4060479489-1+2*2^9*c.k,105624045737989+c.lower,105624429281963+c.upper)) = pointBounds30949 := by
 decide +kernel
def cuts30950 : List PrefixCut := [⟨51,161649396,161649491⟩,
⟨128,409387625,409387860⟩]
theorem checked30950 : checkPrefixCuts (2^48) 4060610561 9 Manual.Count131072.C030950.packed 128 cuts30950 = true := by
 decide +kernel
def pointBounds30950 : List (Nat × Nat × Nat) := [(4060662784,105624617966637,105625001510940)]
theorem point_links_checked30950 : (cuts30950.take 1).map (fun c => (4060610561-1+2*2^9*c.k,105624456317241+c.lower,105624839861449+c.upper)) = pointBounds30950 := by
 decide +kernel
def cuts30951 : List PrefixCut := [⟨47,151038954,151039039⟩,
⟨128,409928966,409929198⟩]
theorem checked30951 : checkPrefixCuts (2^48) 4060741633 9 Manual.Count131072.C030951.packed 128 cuts30951 = true := by
 decide +kernel
def pointBounds30951 : List (Nat × Nat × Nat) := [(4060789760,105625016743820,105625400288348)]
theorem point_links_checked30951 : (cuts30951.take 1).map (fun c => (4060741633-1+2*2^9*c.k,105624865704866+c.lower,105625249249309+c.upper)) = pointBounds30951 := by
 decide +kernel
def cuts30952 : List PrefixCut := [⟨43,136409012,136409086⟩,
⟨128,409638460,409638687⟩]
theorem checked30952 : checkPrefixCuts (2^48) 4060872705 9 Manual.Count131072.C030952.packed 128 cuts30952 = true := by
 decide +kernel
def pointBounds30952 : List (Nat × Nat × Nat) := [(4060916736,105625412042844,105625795587593)]
theorem point_links_checked30952 : (cuts30952.take 1).map (fun c => (4060872705-1+2*2^9*c.k,105625275633832+c.lower,105625659178507+c.upper)) = pointBounds30952 := by
 decide +kernel
def cuts30953 : List PrefixCut := [⟨39,123374144,123374214⟩,
⟨128,409625232,409625456⟩]
theorem checked30953 : checkPrefixCuts (2^48) 4061003777 9 Manual.Count131072.C030953.packed 128 cuts30953 = true := by
 decide +kernel
def pointBounds30953 : List (Nat × Nat × Nat) := [(4061043712,105625808646436,105626192191408)]
theorem point_links_checked30953 : (cuts30953.take 1).map (fun c => (4061003777-1+2*2^9*c.k,105625685272292+c.lower,105626068817194+c.upper)) = pointBounds30953 := by
 decide +kernel
def cuts30954 : List PrefixCut := [⟨35,109161850,109161912⟩,
⟨128,403512948,403513179⟩]
theorem checked30954 : checkPrefixCuts (2^48) 4061134849 9 Manual.Count131072.C030954.packed 128 cuts30954 = true := by
 decide +kernel
def pointBounds30954 : List (Nat × Nat × Nat) := [(4061170688,105626204059374,105626587604562)]
theorem point_links_checked30954 : (cuts30954.take 1).map (fun c => (4061134849-1+2*2^9*c.k,105626094897524+c.lower,105626478442650+c.upper)) = pointBounds30954 := by
 decide +kernel
def cuts30955 : List PrefixCut := [⟨31,103059366,103059424⟩,
⟨128,420410599,420410838⟩]
theorem checked30955 : checkPrefixCuts (2^48) 4061265921 9 Manual.Count131072.C030955.packed 128 cuts30955 = true := by
 decide +kernel
def pointBounds30955 : List (Nat × Nat × Nat) := [(4061297664,105626601469838,105626985015253)]
theorem point_links_checked30955 : (cuts30955.take 1).map (fun c => (4061265921-1+2*2^9*c.k,105626498410472+c.lower,105626881955829+c.upper)) = pointBounds30955 := by
 decide +kernel
def cuts30956 : List PrefixCut := [⟨27,85314101,85314149⟩,
⟨128,411456776,411457008⟩]
theorem checked30956 : checkPrefixCuts (2^48) 4061396993 9 Manual.Count131072.C030956.packed 128 cuts30956 = true := by
 decide +kernel
def pointBounds30956 : List (Nat × Nat × Nat) := [(4061424640,105627004135172,105627387680816)]
theorem point_links_checked30956 : (cuts30956.take 1).map (fun c => (4061396993-1+2*2^9*c.k,105626918821071+c.lower,105627302366667+c.upper)) = pointBounds30956 := by
 decide +kernel
def cuts30957 : List PrefixCut := [⟨23,73044840,73044885⟩,
⟨128,409225873,409226110⟩]
theorem checked30957 : checkPrefixCuts (2^48) 4061528065 9 Manual.Count131072.C030957.packed 128 cuts30957 = true := by
 decide +kernel
def pointBounds30957 : List (Nat × Nat × Nat) := [(4061551616,105627403322687,105627786868560)]
theorem point_links_checked30957 : (cuts30957.take 1).map (fun c => (4061528065-1+2*2^9*c.k,105627330277847+c.lower,105627713823675+c.upper)) = pointBounds30957 := by
 decide +kernel
def cuts30958 : List PrefixCut := [⟨19,62093075,62093110⟩,
⟨128,420716375,420716610⟩]
theorem checked30958 : checkPrefixCuts (2^48) 4061659137 9 Manual.Count131072.C030958.packed 128 cuts30958 = true := by
 decide +kernel
def pointBounds30958 : List (Nat × Nat × Nat) := [(4061678592,105627801596795,105628185142895)]
theorem point_links_checked30958 : (cuts30958.take 1).map (fun c => (4061659137-1+2*2^9*c.k,105627739503720+c.lower,105628123049785+c.upper)) = pointBounds30958 := by
 decide +kernel
def cuts30959 : List PrefixCut := [⟨15,48300781,48300806⟩,
⟨128,405041615,405041849⟩]
theorem checked30959 : checkPrefixCuts (2^48) 4061790209 9 Manual.Count131072.C030959.packed 128 cuts30959 = true := by
 decide +kernel
def pointBounds30959 : List (Nat × Nat × Nat) := [(4061805568,105628208520876,105628592067201)]
theorem point_links_checked30959 : (cuts30959.take 1).map (fun c => (4061790209-1+2*2^9*c.k,105628160220095+c.lower,105628543766395+c.upper)) = pointBounds30959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000029
