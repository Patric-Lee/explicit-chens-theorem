import PlattAssemblyKernel
import PlattCertificates.Count131072.C054000
import PlattCertificates.Count131072.C054001
import PlattCertificates.Count131072.C054002
import PlattCertificates.Count131072.C054003
import PlattCertificates.Count131072.C054004
import PlattCertificates.Count131072.C054005
import PlattCertificates.Count131072.C054006
import PlattCertificates.Count131072.C054007
import PlattCertificates.Count131072.C054008
import PlattCertificates.Count131072.C054009
import PlattCertificates.Count131072.C054010
import PlattCertificates.Count131072.C054011
import PlattCertificates.Count131072.C054012
import PlattCertificates.Count131072.C054013
import PlattCertificates.Count131072.C054014
import PlattCertificates.Count131072.C054015
import PlattCertificates.Count131072.C054016
import PlattCertificates.Count131072.C054017
import PlattCertificates.Count131072.C054018
import PlattCertificates.Count131072.C054019
import PlattCertificates.Count131072.C054020
import PlattCertificates.Count131072.C054021
import PlattCertificates.Count131072.C054022
import PlattCertificates.Count131072.C054023
import PlattCertificates.Count131072.C054024
import PlattCertificates.Count131072.C054025
import PlattCertificates.Count131072.C054026
import PlattCertificates.Count131072.C054027
import PlattCertificates.Count131072.C054028
import PlattCertificates.Count131072.C054029
import PlattCertificates.Count131072.C054030
import PlattCertificates.Count131072.C054031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54000 : List PrefixCut := [⟨59,213315634,213315755⟩,
⟨64,231240816,231240947⟩]
theorem checked54000 : checkPrefixCuts (2^48) 7081820161 10 Manual.Count131072.C054000.packed 64 cuts54000 = true := by
 decide +kernel
def pointBounds54000 : List (Nat × Nat × Nat) := [(7081940992,112613256262591,112613643928163)]
theorem point_links_checked54000 : (cuts54000.take 1).map (fun c => (7081820161-1+2*2^10*c.k,112613042946957+c.lower,112613430612408+c.upper)) = pointBounds54000 := by
 decide +kernel
def cuts54001 : List PrefixCut := [⟨64,230401869,230402004⟩]
theorem checked54001 : checkPrefixCuts (2^48) 7081951233 10 Manual.Count131072.C054001.packed 64 cuts54001 = true := by
 decide +kernel
def cuts54002 : List PrefixCut := [⟨40,146140247,146140330⟩,
⟨64,233179727,233179861⟩]
theorem checked54002 : checkPrefixCuts (2^48) 7082082305 10 Manual.Count131072.C054002.packed 64 cuts54002 = true := by
 decide +kernel
def pointBounds54002 : List (Nat × Nat × Nat) := [(7082164224,112613650729889,112614038395689)]
theorem point_links_checked54002 : (cuts54002.take 1).map (fun c => (7082082305-1+2*2^10*c.k,112613504589642+c.lower,112613892255359+c.upper)) = pointBounds54002 := by
 decide +kernel
def cuts54003 : List PrefixCut := [⟨64,230472854,230472984⟩]
theorem checked54003 : checkPrefixCuts (2^48) 7082213377 10 Manual.Count131072.C054003.packed 64 cuts54003 = true := by
 decide +kernel
def cuts54004 : List PrefixCut := [⟨21,73683635,73683677⟩,
⟨64,231740326,231740459⟩]
theorem checked54004 : checkPrefixCuts (2^48) 7082344449 10 Manual.Count131072.C054004.packed 64 cuts54004 = true := by
 decide +kernel
def pointBounds54004 : List (Nat × Nat × Nat) := [(7082387456,112614041925858,112614429591881)]
theorem point_links_checked54004 : (cuts54004.take 1).map (fun c => (7082344449-1+2*2^10*c.k,112613968242223+c.lower,112614355908204+c.upper)) = pointBounds54004 := by
 decide +kernel
def cuts54005 : List PrefixCut := [⟨64,228516961,228517091⟩]
theorem checked54005 : checkPrefixCuts (2^48) 7082475521 10 Manual.Count131072.C054005.packed 64 cuts54005 = true := by
 decide +kernel
def cuts54006 : List PrefixCut := [⟨2,7908598,7908602⟩,
⟨64,230301074,230301203⟩]
theorem checked54006 : checkPrefixCuts (2^48) 7082606593 10 Manual.Count131072.C054006.packed 64 cuts54006 = true := by
 decide +kernel
def pointBounds54006 : List (Nat × Nat × Nat) := [(7082610688,112614436408108,112614824074356)]
theorem point_links_checked54006 : (cuts54006.take 1).map (fun c => (7082606593-1+2*2^10*c.k,112614428499510+c.lower,112614816165754+c.upper)) = pointBounds54006 := by
 decide +kernel
def cuts54007 : List PrefixCut := [⟨47,169692796,169692889⟩,
⟨64,230018623,230018751⟩]
theorem checked54007 : checkPrefixCuts (2^48) 7082737665 10 Manual.Count131072.C054007.packed 64 cuts54007 = true := by
 decide +kernel
def pointBounds54007 : List (Nat × Nat × Nat) := [(7082833920,112614828493380,112615216159846)]
theorem point_links_checked54007 : (cuts54007.take 1).map (fun c => (7082737665-1+2*2^10*c.k,112614658800584+c.lower,112615046466957+c.upper)) = pointBounds54007 := by
 decide +kernel
def cuts54008 : List PrefixCut := [⟨64,232398753,232398887⟩]
theorem checked54008 : checkPrefixCuts (2^48) 7082868737 10 Manual.Count131072.C054008.packed 64 cuts54008 = true := by
 decide +kernel
def cuts54009 : List PrefixCut := [⟨28,100739240,100739296⟩,
⟨64,231718902,231719034⟩]
theorem checked54009 : checkPrefixCuts (2^48) 7082999809 10 Manual.Count131072.C054009.packed 64 cuts54009 = true := by
 decide +kernel
def pointBounds54009 : List (Nat × Nat × Nat) := [(7083057152,112615221957200,112615609623891)]
theorem point_links_checked54009 : (cuts54009.take 1).map (fun c => (7082999809-1+2*2^10*c.k,112615121217960+c.lower,112615508884595+c.upper)) = pointBounds54009 := by
 decide +kernel
def cuts54010 : List PrefixCut := [⟨64,229409783,229409915⟩]
theorem checked54010 : checkPrefixCuts (2^48) 7083130881 10 Manual.Count131072.C054010.packed 64 cuts54010 = true := by
 decide +kernel
def cuts54011 : List PrefixCut := [⟨9,31830121,31830139⟩,
⟨64,229842653,229842783⟩]
theorem checked54011 : checkPrefixCuts (2^48) 7083261953 10 Manual.Count131072.C054011.packed 64 cuts54011 = true := by
 decide +kernel
def pointBounds54011 : List (Nat × Nat × Nat) := [(7083280384,112615614176766,112616001843683)]
theorem point_links_checked54011 : (cuts54011.take 1).map (fun c => (7083261953-1+2*2^10*c.k,112615582346645+c.lower,112615970013544+c.upper)) = pointBounds54011 := by
 decide +kernel
def cuts54012 : List PrefixCut := [⟨54,192366756,192366866⟩,
⟨64,228566815,228566947⟩]
theorem checked54012 : checkPrefixCuts (2^48) 7083393025 10 Manual.Count131072.C054012.packed 64 cuts54012 = true := by
 decide +kernel
def pointBounds54012 : List (Nat × Nat × Nat) := [(7083503616,112616004556054,112616392223193)]
theorem point_links_checked54012 : (cuts54012.take 1).map (fun c => (7083393025-1+2*2^10*c.k,112615812189298+c.lower,112616199856327+c.upper)) = pointBounds54012 := by
 decide +kernel
def cuts54013 : List PrefixCut := [⟨64,226218150,226218283⟩]
theorem checked54013 : checkPrefixCuts (2^48) 7083524097 10 Manual.Count131072.C054013.packed 64 cuts54013 = true := by
 decide +kernel
def cuts54014 : List PrefixCut := [⟨35,126200353,126200422⟩,
⟨64,229074936,229075063⟩]
theorem checked54014 : checkPrefixCuts (2^48) 7083655169 10 Manual.Count131072.C054014.packed 64 cuts54014 = true := by
 decide +kernel
def pointBounds54014 : List (Nat × Nat × Nat) := [(7083726848,112616393174616,112616780841979)]
theorem point_links_checked54014 : (cuts54014.take 1).map (fun c => (7083655169-1+2*2^10*c.k,112616266974263+c.lower,112616654641557+c.upper)) = pointBounds54014 := by
 decide +kernel
def cuts54015 : List PrefixCut := [⟨64,231653439,231653570⟩]
theorem checked54015 : checkPrefixCuts (2^48) 7083786241 10 Manual.Count131072.C054015.packed 64 cuts54015 = true := by
 decide +kernel
def cuts54016 : List PrefixCut := [⟨16,58449106,58449138⟩,
⟨64,229344594,229344724⟩]
theorem checked54016 : checkPrefixCuts (2^48) 7083917313 10 Manual.Count131072.C054016.packed 64 cuts54016 = true := by
 decide +kernel
def pointBounds54016 : List (Nat × Nat × Nat) := [(7083950080,112616786151744,112617173819328)]
theorem point_links_checked54016 : (cuts54016.take 1).map (fun c => (7083917313-1+2*2^10*c.k,112616727702638+c.lower,112617115370190+c.upper)) = pointBounds54016 := by
 decide +kernel
def cuts54017 : List PrefixCut := [⟨61,215751658,215751784⟩,
⟨64,226161679,226161811⟩]
theorem checked54017 : checkPrefixCuts (2^48) 7084048385 10 Manual.Count131072.C054017.packed 64 cuts54017 = true := by
 decide +kernel
def pointBounds54017 : List (Nat × Nat × Nat) := [(7084173312,112617172798890,112617560466698)]
theorem point_links_checked54017 : (cuts54017.take 1).map (fun c => (7084048385-1+2*2^10*c.k,112616957047232+c.lower,112617344714914+c.upper)) = pointBounds54017 := by
 decide +kernel
def cuts54018 : List PrefixCut := [⟨64,230528073,230528203⟩]
theorem checked54018 : checkPrefixCuts (2^48) 7084179457 10 Manual.Count131072.C054018.packed 64 cuts54018 = true := by
 decide +kernel
def cuts54019 : List PrefixCut := [⟨42,149233063,149233148⟩,
⟨64,227663128,227663257⟩]
theorem checked54019 : checkPrefixCuts (2^48) 7084310529 10 Manual.Count131072.C054019.packed 64 cuts54019 = true := by
 decide +kernel
def pointBounds54019 : List (Nat × Nat × Nat) := [(7084396544,112617562970047,112617950638076)]
theorem point_links_checked54019 : (cuts54019.take 1).map (fun c => (7084310529-1+2*2^10*c.k,112617413736984+c.lower,112617801404928+c.upper)) = pointBounds54019 := by
 decide +kernel
def cuts54020 : List PrefixCut := [⟨64,229327617,229327749⟩]
theorem checked54020 : checkPrefixCuts (2^48) 7084441601 10 Manual.Count131072.C054020.packed 64 cuts54020 = true := by
 decide +kernel
def cuts54021 : List PrefixCut := [⟨23,82639542,82639590⟩,
⟨64,228846618,228846752⟩]
theorem checked54021 : checkPrefixCuts (2^48) 7084572673 10 Manual.Count131072.C054021.packed 64 cuts54021 = true := by
 decide +kernel
def pointBounds54021 : List (Nat × Nat × Nat) := [(7084619776,112617953367271,112618341035524)]
theorem point_links_checked54021 : (cuts54021.take 1).map (fun c => (7084572673-1+2*2^10*c.k,112617870727729+c.lower,112618258395934+c.upper)) = pointBounds54021 := by
 decide +kernel
def cuts54022 : List PrefixCut := [⟨64,230471292,230471423⟩]
theorem checked54022 : checkPrefixCuts (2^48) 7084703745 10 Manual.Count131072.C054022.packed 64 cuts54022 = true := by
 decide +kernel
def cuts54023 : List PrefixCut := [⟨4,14461424,14461433⟩,
⟨64,230308109,230308242⟩]
theorem checked54023 : checkPrefixCuts (2^48) 7084834817 10 Manual.Count131072.C054023.packed 64 cuts54023 = true := by
 decide +kernel
def pointBounds54023 : List (Nat × Nat × Nat) := [(7084843008,112618344507063,112618732175542)]
theorem point_links_checked54023 : (cuts54023.take 1).map (fun c => (7084834817-1+2*2^10*c.k,112618330045639+c.lower,112618717714109+c.upper)) = pointBounds54023 := by
 decide +kernel
def cuts54024 : List PrefixCut := [⟨49,175916448,175916546⟩,
⟨64,231575134,231575264⟩]
theorem checked54024 : checkPrefixCuts (2^48) 7084965889 10 Manual.Count131072.C054024.packed 64 cuts54024 = true := by
 decide +kernel
def pointBounds54024 : List (Nat × Nat × Nat) := [(7085066240,112618736270196,112619123938897)]
theorem point_links_checked54024 : (cuts54024.take 1).map (fun c => (7084965889-1+2*2^10*c.k,112618560353748+c.lower,112618948022351+c.upper)) = pointBounds54024 := by
 decide +kernel
def cuts54025 : List PrefixCut := [⟨64,230220134,230220266⟩]
theorem checked54025 : checkPrefixCuts (2^48) 7085096961 10 Manual.Count131072.C054025.packed 64 cuts54025 = true := by
 decide +kernel
def cuts54026 : List PrefixCut := [⟨30,108454249,108454311⟩,
⟨64,231963835,231963967⟩]
theorem checked54026 : checkPrefixCuts (2^48) 7085228033 10 Manual.Count131072.C054026.packed 64 cuts54026 = true := by
 decide +kernel
def pointBounds54026 : List (Nat × Nat × Nat) := [(7085289472,112619130603265,112619518272192)]
theorem point_links_checked54026 : (cuts54026.take 1).map (fun c => (7085228033-1+2*2^10*c.k,112619022149016+c.lower,112619409817881+c.upper)) = pointBounds54026 := by
 decide +kernel
def cuts54027 : List PrefixCut := [⟨64,230648597,230648730⟩]
theorem checked54027 : checkPrefixCuts (2^48) 7085359105 10 Manual.Count131072.C054027.packed 64 cuts54027 = true := by
 decide +kernel
def cuts54028 : List PrefixCut := [⟨11,39844649,39844672⟩,
⟨64,231994984,231995115⟩]
theorem checked54028 : checkPrefixCuts (2^48) 7085490177 10 Manual.Count131072.C054028.packed 64 cuts54028 = true := by
 decide +kernel
def pointBounds54028 : List (Nat × Nat × Nat) := [(7085512704,112619524606097,112619912275250)]
theorem point_links_checked54028 : (cuts54028.take 1).map (fun c => (7085490177-1+2*2^10*c.k,112619484761448+c.lower,112619872430578+c.upper)) = pointBounds54028 := by
 decide +kernel
def cuts54029 : List PrefixCut := [⟨56,203667410,203667524⟩,
⟨64,232268772,232268902⟩]
theorem checked54029 : checkPrefixCuts (2^48) 7085621249 10 Manual.Count131072.C054029.packed 64 cuts54029 = true := by
 decide +kernel
def pointBounds54029 : List (Nat × Nat × Nat) := [(7085735936,112619920423842,112620308093217)]
theorem point_links_checked54029 : (cuts54029.take 1).map (fun c => (7085621249-1+2*2^10*c.k,112619716756432+c.lower,112620104425693+c.upper)) = pointBounds54029 := by
 decide +kernel
def cuts54030 : List PrefixCut := [⟨64,227100380,227100511⟩]
theorem checked54030 : checkPrefixCuts (2^48) 7085752321 10 Manual.Count131072.C054030.packed 64 cuts54030 = true := by
 decide +kernel
def cuts54031 : List PrefixCut := [⟨37,130530176,130530248⟩,
⟨64,229837058,229837186⟩]
theorem checked54031 : checkPrefixCuts (2^48) 7085883393 10 Manual.Count131072.C054031.packed 64 cuts54031 = true := by
 decide +kernel
def pointBounds54031 : List (Nat × Nat × Nat) := [(7085959168,112620306655760,112620694325354)]
theorem point_links_checked54031 : (cuts54031.take 1).map (fun c => (7085883393-1+2*2^10*c.k,112620176125584+c.lower,112620563795106+c.upper)) = pointBounds54031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000125
