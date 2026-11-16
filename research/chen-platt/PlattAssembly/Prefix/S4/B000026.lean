import PlattAssemblyKernel
import PlattCertificates.Count131072.C030832
import PlattCertificates.Count131072.C030833
import PlattCertificates.Count131072.C030834
import PlattCertificates.Count131072.C030835
import PlattCertificates.Count131072.C030836
import PlattCertificates.Count131072.C030837
import PlattCertificates.Count131072.C030838
import PlattCertificates.Count131072.C030839
import PlattCertificates.Count131072.C030840
import PlattCertificates.Count131072.C030841
import PlattCertificates.Count131072.C030842
import PlattCertificates.Count131072.C030843
import PlattCertificates.Count131072.C030844
import PlattCertificates.Count131072.C030845
import PlattCertificates.Count131072.C030846
import PlattCertificates.Count131072.C030847
import PlattCertificates.Count131072.C030848
import PlattCertificates.Count131072.C030849
import PlattCertificates.Count131072.C030850
import PlattCertificates.Count131072.C030851
import PlattCertificates.Count131072.C030852
import PlattCertificates.Count131072.C030853
import PlattCertificates.Count131072.C030854
import PlattCertificates.Count131072.C030855
import PlattCertificates.Count131072.C030856
import PlattCertificates.Count131072.C030857
import PlattCertificates.Count131072.C030858
import PlattCertificates.Count131072.C030859
import PlattCertificates.Count131072.C030860
import PlattCertificates.Count131072.C030861
import PlattCertificates.Count131072.C030862
import PlattCertificates.Count131072.C030863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30832 : List PrefixCut := [⟨27,87048544,87048592⟩,
⟨128,411092093,411092322⟩]
theorem checked30832 : checkPrefixCuts (2^48) 4045144065 9 Manual.Count131072.C030832.packed 128 cuts30832 = true := by
 decide +kernel
def pointBounds30832 : List (Nat × Nat × Nat) := [(4045171712,105575962804126,105576346321038)]
theorem point_links_checked30832 : (cuts30832.take 1).map (fun c => (4045144065-1+2*2^9*c.k,105575875755582+c.lower,105576259272446+c.upper)) = pointBounds30832 := by
 decide +kernel
def cuts30833 : List PrefixCut := [⟨23,73686219,73686261⟩,
⟨128,411148364,411148603⟩]
theorem checked30833 : checkPrefixCuts (2^48) 4045275137 9 Manual.Count131072.C030833.packed 128 cuts30833 = true := by
 decide +kernel
def pointBounds30833 : List (Nat × Nat × Nat) := [(4045298688,105576360533894,105576744051029)]
theorem point_links_checked30833 : (cuts30833.take 1).map (fun c => (4045275137-1+2*2^9*c.k,105576286847675+c.lower,105576670364768+c.upper)) = pointBounds30833 := by
 decide +kernel
def cuts30834 : List PrefixCut := [⟨19,61298864,61298897⟩,
⟨128,412665761,412665994⟩]
theorem checked30834 : checkPrefixCuts (2^48) 4045406209 9 Manual.Count131072.C030834.packed 128 cuts30834 = true := by
 decide +kernel
def pointBounds30834 : List (Nat × Nat × Nat) := [(4045425664,105576759294903,105577142812268)]
theorem point_links_checked30834 : (cuts30834.take 1).map (fun c => (4045406209-1+2*2^9*c.k,105576697996039+c.lower,105577081513371+c.upper)) = pointBounds30834 := by
 decide +kernel
def cuts30835 : List PrefixCut := [⟨15,48703556,48703584⟩,
⟨128,411608762,411608999⟩]
theorem checked30835 : checkPrefixCuts (2^48) 4045537281 9 Manual.Count131072.C030835.packed 128 cuts30835 = true := by
 decide +kernel
def pointBounds30835 : List (Nat × Nat × Nat) := [(4045552640,105577159365356,105577542882949)]
theorem point_links_checked30835 : (cuts30835.take 1).map (fun c => (4045537281-1+2*2^9*c.k,105577110661800+c.lower,105577494179365+c.upper)) = pointBounds30835 := by
 decide +kernel
def cuts30836 : List PrefixCut := [⟨11,35204590,35204610⟩,
⟨128,410830045,410830274⟩]
theorem checked30836 : checkPrefixCuts (2^48) 4045668353 9 Manual.Count131072.C030836.packed 128 cuts30836 = true := by
 decide +kernel
def pointBounds30836 : List (Nat × Nat × Nat) := [(4045679616,105577557475152,105577940992974)]
theorem point_links_checked30836 : (cuts30836.take 1).map (fun c => (4045668353-1+2*2^9*c.k,105577522270562+c.lower,105577905788364+c.upper)) = pointBounds30836 := by
 decide +kernel
def cuts30837 : List PrefixCut := [⟨7,22054346,22054360⟩,
⟨128,411651653,411651889⟩]
theorem checked30837 : checkPrefixCuts (2^48) 4045799425 9 Manual.Count131072.C030837.packed 128 cuts30837 = true := by
 decide +kernel
def pointBounds30837 : List (Nat × Nat × Nat) := [(4045806592,105577955154953,105578338672998)]
theorem point_links_checked30837 : (cuts30837.take 1).map (fun c => (4045799425-1+2*2^9*c.k,105577933100607+c.lower,105578316618638+c.upper)) = pointBounds30837 := by
 decide +kernel
def cuts30838 : List PrefixCut := [⟨3,9461501,9461504⟩,
⟨127,406211997,406212213⟩,
⟨128,409272973,409273191⟩]
theorem checked30838 : checkPrefixCuts (2^48) 4045930497 9 Manual.Count131072.C030838.packed 128 cuts30838 = true := by
 decide +kernel
def pointBounds30838 : List (Nat × Nat × Nat) := [(4045933568,105578354213761,105578737732031),(4046060544,105578750964257,105579134482740)]
theorem point_links_checked30838 : (cuts30838.take 2).map (fun c => (4045930497-1+2*2^9*c.k,105578344752260+c.lower,105578728270527+c.upper)) = pointBounds30838 := by
 decide +kernel
def cuts30839 : List PrefixCut := [⟨123,402372877,402373094⟩,
⟨128,417677269,417677495⟩]
theorem checked30839 : checkPrefixCuts (2^48) 4046061569 9 Manual.Count131072.C030839.packed 128 cuts30839 = true := by
 decide +kernel
def pointBounds30839 : List (Nat × Nat × Nat) := [(4046187520,105579156398110,105579539916812)]
theorem point_links_checked30839 : (cuts30839.take 1).map (fun c => (4046061569-1+2*2^9*c.k,105578754025233+c.lower,105579137543718+c.upper)) = pointBounds30839 := by
 decide +kernel
def cuts30840 : List PrefixCut := [⟨119,385316820,385317033⟩,
⟨128,415855064,415855294⟩]
theorem checked30840 : checkPrefixCuts (2^48) 4046192641 9 Manual.Count131072.C030840.packed 128 cuts30840 = true := by
 decide +kernel
def pointBounds30840 : List (Nat × Nat × Nat) := [(4046314496,105579557019322,105579940538246)]
theorem point_links_checked30840 : (cuts30840.take 1).map (fun c => (4046192641-1+2*2^9*c.k,105579171702502+c.lower,105579555221213+c.upper)) = pointBounds30840 := by
 decide +kernel
def cuts30841 : List PrefixCut := [⟨115,371252950,371253159⟩,
⟨128,413337346,413337579⟩]
theorem checked30841 : checkPrefixCuts (2^48) 4046323713 9 Manual.Count131072.C030841.packed 128 cuts30841 = true := by
 decide +kernel
def pointBounds30841 : List (Nat × Nat × Nat) := [(4046441472,105579958810516,105580342329666)]
theorem point_links_checked30841 : (cuts30841.take 1).map (fun c => (4046323713-1+2*2^9*c.k,105579587557566+c.lower,105579971076507+c.upper)) = pointBounds30841 := by
 decide +kernel
def cuts30842 : List PrefixCut := [⟨111,355590122,355590326⟩,
⟨128,410193748,410193985⟩]
theorem checked30842 : checkPrefixCuts (2^48) 4046454785 9 Manual.Count131072.C030842.packed 128 cuts30842 = true := by
 decide +kernel
def pointBounds30842 : List (Nat × Nat × Nat) := [(4046568448,105580356485034,105580740004412)]
theorem point_links_checked30842 : (cuts30842.take 1).map (fun c => (4046454785-1+2*2^9*c.k,105580000894912+c.lower,105580384414086+c.upper)) = pointBounds30842 := by
 decide +kernel
def cuts30843 : List PrefixCut := [⟨107,346953636,346953833⟩,
⟨128,414910377,414910612⟩]
theorem checked30843 : checkPrefixCuts (2^48) 4046585857 9 Manual.Count131072.C030843.packed 128 cuts30843 = true := by
 decide +kernel
def pointBounds30843 : List (Nat × Nat × Nat) := [(4046695424,105580758042296,105581141561904)]
theorem point_links_checked30843 : (cuts30843.take 1).map (fun c => (4046585857-1+2*2^9*c.k,105580411088660+c.lower,105580794608071+c.upper)) = pointBounds30843 := by
 decide +kernel
def cuts30844 : List PrefixCut := [⟨103,336787493,336787685⟩,
⟨128,416148980,416149216⟩]
theorem checked30844 : checkPrefixCuts (2^48) 4046716929 9 Manual.Count131072.C030844.packed 128 cuts30844 = true := by
 decide +kernel
def pointBounds30844 : List (Nat × Nat × Nat) := [(4046822400,105581162786530,105581546306368)]
theorem point_links_checked30844 : (cuts30844.take 1).map (fun c => (4046716929-1+2*2^9*c.k,105580825999037+c.lower,105581209518683+c.upper)) = pointBounds30844 := by
 decide +kernel
def cuts30845 : List PrefixCut := [⟨99,315910786,315910965⟩,
⟨128,407719569,407719799⟩]
theorem checked30845 : checkPrefixCuts (2^48) 4046848001 9 Manual.Count131072.C030845.packed 128 cuts30845 = true := by
 decide +kernel
def pointBounds30845 : List (Nat × Nat × Nat) := [(4046949376,105581558058803,105581941578864)]
theorem point_links_checked30845 : (cuts30845.take 1).map (fun c => (4046848001-1+2*2^9*c.k,105581242148017+c.lower,105581625667899+c.upper)) = pointBounds30845 := by
 decide +kernel
def cuts30846 : List PrefixCut := [⟨95,306094014,306094181⟩,
⟨128,410488398,410488628⟩]
theorem checked30846 : checkPrefixCuts (2^48) 4046979073 9 Manual.Count131072.C030846.packed 128 cuts30846 = true := by
 decide +kernel
def pointBounds30846 : List (Nat × Nat × Nat) := [(4047076352,105581955961600,105582339481879)]
theorem point_links_checked30846 : (cuts30846.take 1).map (fun c => (4046979073-1+2*2^9*c.k,105581649867586+c.lower,105582033387698+c.upper)) = pointBounds30846 := by
 decide +kernel
def cuts30847 : List PrefixCut := [⟨91,293913223,293913384⟩,
⟨128,409640555,409640779⟩]
theorem checked30847 : checkPrefixCuts (2^48) 4047110145 9 Manual.Count131072.C030847.packed 128 cuts30847 = true := by
 decide +kernel
def pointBounds30847 : List (Nat × Nat × Nat) := [(4047203328,105582354269207,105582737789710)]
theorem point_links_checked30847 : (cuts30847.take 1).map (fun c => (4047110145-1+2*2^9*c.k,105582060355984+c.lower,105582443876326+c.upper)) = pointBounds30847 := by
 decide +kernel
def cuts30848 : List PrefixCut := [⟨87,282498212,282498366⟩,
⟨128,415677752,415677981⟩]
theorem checked30848 : checkPrefixCuts (2^48) 4047241217 9 Manual.Count131072.C030848.packed 128 cuts30848 = true := by
 decide +kernel
def pointBounds30848 : List (Nat × Nat × Nat) := [(4047330304,105582752494751,105583136015471)]
theorem point_links_checked30848 : (cuts30848.take 1).map (fun c => (4047241217-1+2*2^9*c.k,105582469996539+c.lower,105582853517105+c.upper)) = pointBounds30848 := by
 decide +kernel
def cuts30849 : List PrefixCut := [⟨83,265729014,265729167⟩,
⟨128,413021584,413021822⟩]
theorem checked30849 : checkPrefixCuts (2^48) 4047372289 9 Manual.Count131072.C030849.packed 128 cuts30849 = true := by
 decide +kernel
def pointBounds30849 : List (Nat × Nat × Nat) := [(4047457280,105583151403305,105583534924253)]
theorem point_links_checked30849 : (cuts30849.take 1).map (fun c => (4047372289-1+2*2^9*c.k,105582885674291+c.lower,105583269195086+c.upper)) = pointBounds30849 := by
 decide +kernel
def cuts30850 : List PrefixCut := [⟨79,252924800,252924941⟩,
⟨128,412660550,412660777⟩]
theorem checked30850 : checkPrefixCuts (2^48) 4047503361 9 Manual.Count131072.C030850.packed 128 cuts30850 = true := by
 decide +kernel
def pointBounds30850 : List (Nat × Nat × Nat) := [(4047584256,105583551620675,105583935141849)]
theorem point_links_checked30850 : (cuts30850.take 1).map (fun c => (4047503361-1+2*2^9*c.k,105583298695875+c.lower,105583682216908+c.upper)) = pointBounds30850 := by
 decide +kernel
def cuts30851 : List PrefixCut := [⟨75,244502426,244502560⟩,
⟨128,413968500,413968728⟩]
theorem checked30851 : checkPrefixCuts (2^48) 4047634433 9 Manual.Count131072.C030851.packed 128 cuts30851 = true := by
 decide +kernel
def pointBounds30851 : List (Nat × Nat × Nat) := [(4047711232,105583955858851,105584339380245)]
theorem point_links_checked30851 : (cuts30851.take 1).map (fun c => (4047634433-1+2*2^9*c.k,105583711356425+c.lower,105584094877685+c.upper)) = pointBounds30851 := by
 decide +kernel
def cuts30852 : List PrefixCut := [⟨71,228014153,228014287⟩,
⟨128,408948361,408948600⟩]
theorem checked30852 : checkPrefixCuts (2^48) 4047765505 9 Manual.Count131072.C030852.packed 128 cuts30852 = true := by
 decide +kernel
def pointBounds30852 : List (Nat × Nat × Nat) := [(4047838208,105584353339078,105584736860700)]
theorem point_links_checked30852 : (cuts30852.take 1).map (fun c => (4047765505-1+2*2^9*c.k,105584125324925+c.lower,105584508846413+c.upper)) = pointBounds30852 := by
 decide +kernel
def cuts30853 : List PrefixCut := [⟨67,216533553,216533682⟩,
⟨128,413176758,413176998⟩]
theorem checked30853 : checkPrefixCuts (2^48) 4047896577 9 Manual.Count131072.C030853.packed 128 cuts30853 = true := by
 decide +kernel
def pointBounds30853 : List (Nat × Nat × Nat) := [(4047965184,105584750806839,105585134328695)]
theorem point_links_checked30853 : (cuts30853.take 1).map (fun c => (4047896577-1+2*2^9*c.k,105584534273286+c.lower,105584917795013+c.upper)) = pointBounds30853 := by
 decide +kernel
def cuts30854 : List PrefixCut := [⟨63,204288785,204288899⟩,
⟨128,410034467,410034699⟩]
theorem checked30854 : checkPrefixCuts (2^48) 4048027649 9 Manual.Count131072.C030854.packed 128 cuts30854 = true := by
 decide +kernel
def pointBounds30854 : List (Nat × Nat × Nat) := [(4048092160,105585151738829,105585535260910)]
theorem point_links_checked30854 : (cuts30854.take 1).map (fun c => (4048027649-1+2*2^9*c.k,105584947450044+c.lower,105585330972011+c.upper)) = pointBounds30854 := by
 decide +kernel
def cuts30855 : List PrefixCut := [⟨59,186621377,186621486⟩,
⟨128,406544575,406544810⟩]
theorem checked30855 : checkPrefixCuts (2^48) 4048158721 9 Manual.Count131072.C030855.packed 128 cuts30855 = true := by
 decide +kernel
def pointBounds30855 : List (Nat × Nat × Nat) := [(4048219136,105585544105888,105585927628196)]
theorem point_links_checked30855 : (cuts30855.take 1).map (fun c => (4048158721-1+2*2^9*c.k,105585357484511+c.lower,105585741006710+c.upper)) = pointBounds30855 := by
 decide +kernel
def cuts30856 : List PrefixCut := [⟨55,178550099,178550195⟩,
⟨128,416473978,416474204⟩]
theorem checked30856 : checkPrefixCuts (2^48) 4048289793 9 Manual.Count131072.C030856.packed 128 cuts30856 = true := by
 decide +kernel
def pointBounds30856 : List (Nat × Nat × Nat) := [(4048346112,105585942579185,105586326101715)]
theorem point_links_checked30856 : (cuts30856.take 1).map (fun c => (4048289793-1+2*2^9*c.k,105585764029086+c.lower,105586147551520+c.upper)) = pointBounds30856 := by
 decide +kernel
def cuts30857 : List PrefixCut := [⟨51,162136113,162136208⟩,
⟨128,411663175,411663411⟩]
theorem checked30857 : checkPrefixCuts (2^48) 4048420865 9 Manual.Count131072.C030857.packed 128 cuts30857 = true := by
 decide +kernel
def pointBounds30857 : List (Nat × Nat × Nat) := [(4048473088,105586342639177,105586726161932)]
theorem point_links_checked30857 : (cuts30857.take 1).map (fun c => (4048420865-1+2*2^9*c.k,105586180503064+c.lower,105586564025724+c.upper)) = pointBounds30857 := by
 decide +kernel
def cuts30858 : List PrefixCut := [⟨47,153162302,153162388⟩,
⟨128,420757481,420757716⟩]
theorem checked30858 : checkPrefixCuts (2^48) 4048551937 9 Manual.Count131072.C030858.packed 128 cuts30858 = true := by
 decide +kernel
def pointBounds30858 : List (Nat × Nat × Nat) := [(4048600064,105586745328541,105587128851523)]
theorem point_links_checked30858 : (cuts30858.take 1).map (fun c => (4048551937-1+2*2^9*c.k,105586592166239+c.lower,105586975689135+c.upper)) = pointBounds30858 := by
 decide +kernel
def cuts30859 : List PrefixCut := [⟨43,137653978,137654058⟩,
⟨128,410732770,410733003⟩]
theorem checked30859 : checkPrefixCuts (2^48) 4048683009 9 Manual.Count131072.C030859.packed 128 cuts30859 = true := by
 decide +kernel
def pointBounds30859 : List (Nat × Nat × Nat) := [(4048727040,105587150577698,105587534100909)]
theorem point_links_checked30859 : (cuts30859.take 1).map (fun c => (4048683009-1+2*2^9*c.k,105587012923720+c.lower,105587396446851+c.upper)) = pointBounds30859 := by
 decide +kernel
def cuts30860 : List PrefixCut := [⟨39,125066458,125066529⟩,
⟨128,405575074,405575299⟩]
theorem checked30860 : checkPrefixCuts (2^48) 4048814081 9 Manual.Count131072.C030860.packed 128 cuts30860 = true := by
 decide +kernel
def pointBounds30860 : List (Nat × Nat × Nat) := [(4048854016,105587548722948,105587932246383)]
theorem point_links_checked30860 : (cuts30860.take 1).map (fun c => (4048814081-1+2*2^9*c.k,105587423656490+c.lower,105587807179854+c.upper)) = pointBounds30860 := by
 decide +kernel
def cuts30861 : List PrefixCut := [⟨35,111576030,111576093⟩,
⟨128,405770472,405770704⟩]
theorem checked30861 : checkPrefixCuts (2^48) 4048945153 9 Manual.Count131072.C030861.packed 128 cuts30861 = true := by
 decide +kernel
def pointBounds30861 : List (Nat × Nat × Nat) := [(4048980992,105587940807594,105588324331246)]
theorem point_links_checked30861 : (cuts30861.take 1).map (fun c => (4048945153-1+2*2^9*c.k,105587829231564+c.lower,105588212755153+c.upper)) = pointBounds30861 := by
 decide +kernel
def cuts30862 : List PrefixCut := [⟨31,98990156,98990216⟩,
⟨128,410623363,410623600⟩]
theorem checked30862 : checkPrefixCuts (2^48) 4049076225 9 Manual.Count131072.C030862.packed 128 cuts30862 = true := by
 decide +kernel
def pointBounds30862 : List (Nat × Nat × Nat) := [(4049107968,105588333992192,105588717516073)]
theorem point_links_checked30862 : (cuts30862.take 1).map (fun c => (4049076225-1+2*2^9*c.k,105588235002036+c.lower,105588618525857+c.upper)) = pointBounds30862 := by
 decide +kernel
def cuts30863 : List PrefixCut := [⟨27,88838053,88838101⟩,
⟨128,416935680,416935909⟩]
theorem checked30863 : checkPrefixCuts (2^48) 4049207297 9 Manual.Count131072.C030863.packed 128 cuts30863 = true := by
 decide +kernel
def pointBounds30863 : List (Nat × Nat × Nat) := [(4049234944,105588734463452,105589117987558)]
theorem point_links_checked30863 : (cuts30863.take 1).map (fun c => (4049207297-1+2*2^9*c.k,105588645625399+c.lower,105589029149457+c.upper)) = pointBounds30863 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000026
