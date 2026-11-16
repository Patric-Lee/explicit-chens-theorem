import PlattAssemblyKernel
import PlattCertificates.Count131072.C036816
import PlattCertificates.Count131072.C036817
import PlattCertificates.Count131072.C036818
import PlattCertificates.Count131072.C036819
import PlattCertificates.Count131072.C036820
import PlattCertificates.Count131072.C036821
import PlattCertificates.Count131072.C036822
import PlattCertificates.Count131072.C036823
import PlattCertificates.Count131072.C036824
import PlattCertificates.Count131072.C036825
import PlattCertificates.Count131072.C036826
import PlattCertificates.Count131072.C036827
import PlattCertificates.Count131072.C036828
import PlattCertificates.Count131072.C036829
import PlattCertificates.Count131072.C036830
import PlattCertificates.Count131072.C036831
import PlattCertificates.Count131072.C036832
import PlattCertificates.Count131072.C036833
import PlattCertificates.Count131072.C036834
import PlattCertificates.Count131072.C036835
import PlattCertificates.Count131072.C036836
import PlattCertificates.Count131072.C036837
import PlattCertificates.Count131072.C036838
import PlattCertificates.Count131072.C036839
import PlattCertificates.Count131072.C036840
import PlattCertificates.Count131072.C036841
import PlattCertificates.Count131072.C036842
import PlattCertificates.Count131072.C036843
import PlattCertificates.Count131072.C036844
import PlattCertificates.Count131072.C036845
import PlattCertificates.Count131072.C036846
import PlattCertificates.Count131072.C036847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000213
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36816 : List PrefixCut := [⟨64,338384581,338384788⟩]
theorem checked36816 : checkPrefixCuts (2^48) 4829478913 10 Manual.Count131072.C036816.packed 64 cuts36816 = true := by
 decide +kernel
def cuts36817 : List PrefixCut := [⟨5,27566922,27566938⟩,
⟨64,344203406,344203616⟩]
theorem checked36817 : checkPrefixCuts (2^48) 4829609985 10 Manual.Count131072.C036817.packed 64 cuts36817 = true := by
 decide +kernel
def pointBounds36817 : List (Nat × Nat × Nat) := [(4829620224,107822317229354,107822702106308)]
theorem point_links_checked36817 : (cuts36817.take 1).map (fun c => (4829609985-1+2*2^10*c.k,107822289662432+c.lower,107822674539370+c.upper)) = pointBounds36817 := by
 decide +kernel
def cuts36818 : List PrefixCut := [⟨15,82523504,82523554⟩,
⟨64,343902686,343902893⟩]
theorem checked36818 : checkPrefixCuts (2^48) 4829741057 10 Manual.Count131072.C036818.packed 64 cuts36818 = true := by
 decide +kernel
def pointBounds36818 : List (Nat × Nat × Nat) := [(4829771776,107822716389342,107823101266540)]
theorem point_links_checked36818 : (cuts36818.take 1).map (fun c => (4829741057-1+2*2^10*c.k,107822633865838+c.lower,107823018742986+c.upper)) = pointBounds36818 := by
 decide +kernel
def cuts36819 : List PrefixCut := [⟨25,131299447,131299527⟩,
⟨64,336958351,336958558⟩]
theorem checked36819 : checkPrefixCuts (2^48) 4829872129 10 Manual.Count131072.C036819.packed 64 cuts36819 = true := by
 decide +kernel
def pointBounds36819 : List (Nat × Nat × Nat) := [(4829923328,107823109067971,107823493945406)]
theorem point_links_checked36819 : (cuts36819.take 1).map (fun c => (4829872129-1+2*2^10*c.k,107822977768524+c.lower,107823362645879+c.upper)) = pointBounds36819 := by
 decide +kernel
def cuts36820 : List PrefixCut := [⟨35,183977032,183977147⟩,
⟨64,337881604,337881814⟩]
theorem checked36820 : checkPrefixCuts (2^48) 4830003201 10 Manual.Count131072.C036820.packed 64 cuts36820 = true := by
 decide +kernel
def pointBounds36820 : List (Nat × Nat × Nat) := [(4830074880,107823498703907,107823883581584)]
theorem point_links_checked36820 : (cuts36820.take 1).map (fun c => (4830003201-1+2*2^10*c.k,107823314726875+c.lower,107823699604437+c.upper)) = pointBounds36820 := by
 decide +kernel
def cuts36821 : List PrefixCut := [⟨45,245334361,245334512⟩,
⟨64,349119297,349119509⟩]
theorem checked36821 : checkPrefixCuts (2^48) 4830134273 10 Manual.Count131072.C036821.packed 64 cuts36821 = true := by
 decide +kernel
def pointBounds36821 : List (Nat × Nat × Nat) := [(4830226432,107823897942840,107824282820763)]
theorem point_links_checked36821 : (cuts36821.take 1).map (fun c => (4830134273-1+2*2^10*c.k,107823652608479+c.lower,107824037486251+c.upper)) = pointBounds36821 := by
 decide +kernel
def cuts36822 : List PrefixCut := [⟨55,294334368,294334549⟩,
⟨64,341709263,341709472⟩]
theorem checked36822 : checkPrefixCuts (2^48) 4830265345 10 Manual.Count131072.C036822.packed 64 cuts36822 = true := by
 decide +kernel
def pointBounds36822 : List (Nat × Nat × Nat) := [(4830377984,107824296062144,107824680940309)]
theorem point_links_checked36822 : (cuts36822.take 1).map (fun c => (4830265345-1+2*2^10*c.k,107824001727776+c.lower,107824386605760+c.upper)) = pointBounds36822 := by
 decide +kernel
def cuts36823 : List PrefixCut := [⟨64,342748825,342749036⟩]
theorem checked36823 : checkPrefixCuts (2^48) 4830396417 10 Manual.Count131072.C036823.packed 64 cuts36823 = true := by
 decide +kernel
def cuts36824 : List PrefixCut := [⟨1,4778140,4778143⟩,
⟨64,341107979,341108191⟩]
theorem checked36824 : checkPrefixCuts (2^48) 4830527489 10 Manual.Count131072.C036824.packed 64 cuts36824 = true := by
 decide +kernel
def pointBounds36824 : List (Nat × Nat × Nat) := [(4830529536,107824690964004,107825075842411)]
theorem point_links_checked36824 : (cuts36824.take 1).map (fun c => (4830527489-1+2*2^10*c.k,107824686185864+c.lower,107825071064268+c.upper)) = pointBounds36824 := by
 decide +kernel
def cuts36825 : List PrefixCut := [⟨11,59550203,59550238⟩,
⟨64,342613747,342613959⟩]
theorem checked36825 : checkPrefixCuts (2^48) 4830658561 10 Manual.Count131072.C036825.packed 64 cuts36825 = true := by
 decide +kernel
def pointBounds36825 : List (Nat × Nat × Nat) := [(4830681088,107825086844046,107825471722697)]
theorem point_links_checked36825 : (cuts36825.take 1).map (fun c => (4830658561-1+2*2^10*c.k,107825027293843+c.lower,107825412172459+c.upper)) = pointBounds36825 := by
 decide +kernel
def cuts36826 : List PrefixCut := [⟨21,110589984,110590050⟩,
⟨64,337535257,337535463⟩]
theorem checked36826 : checkPrefixCuts (2^48) 4830789633 10 Manual.Count131072.C036826.packed 64 cuts36826 = true := by
 decide +kernel
def pointBounds36826 : List (Nat × Nat × Nat) := [(4830832640,107825480497574,107825865376468)]
theorem point_links_checked36826 : (cuts36826.take 1).map (fun c => (4830789633-1+2*2^10*c.k,107825369907590+c.lower,107825754786418+c.upper)) = pointBounds36826 := by
 decide +kernel
def cuts36827 : List PrefixCut := [⟨31,169259494,169259597⟩,
⟨64,346440604,346440813⟩]
theorem checked36827 : checkPrefixCuts (2^48) 4830920705 10 Manual.Count131072.C036827.packed 64 cuts36827 = true := by
 decide +kernel
def pointBounds36827 : List (Nat × Nat × Nat) := [(4830984192,107825876702341,107826261581478)]
theorem point_links_checked36827 : (cuts36827.take 1).map (fun c => (4830920705-1+2*2^10*c.k,107825707442847+c.lower,107826092321881+c.upper)) = pointBounds36827 := by
 decide +kernel
def cuts36828 : List PrefixCut := [⟨41,216622503,216622635⟩,
⟨64,341362294,341362500⟩]
theorem checked36828 : checkPrefixCuts (2^48) 4831051777 10 Manual.Count131072.C036828.packed 64 cuts36828 = true := by
 decide +kernel
def pointBounds36828 : List (Nat × Nat × Nat) := [(4831135744,107826270505954,107826655385329)]
theorem point_links_checked36828 : (cuts36828.take 1).map (fun c => (4831051777-1+2*2^10*c.k,107826053883451+c.lower,107826438762694+c.upper)) = pointBounds36828 := by
 decide +kernel
def cuts36829 : List PrefixCut := [⟨51,273362861,273363024⟩,
⟨64,343974811,343975016⟩]
theorem checked36829 : checkPrefixCuts (2^48) 4831182849 10 Manual.Count131072.C036829.packed 64 cuts36829 = true := by
 decide +kernel
def pointBounds36829 : List (Nat × Nat × Nat) := [(4831287296,107826668608606,107827053488218)]
theorem point_links_checked36829 : (cuts36829.take 1).map (fun c => (4831182849-1+2*2^10*c.k,107826395245745+c.lower,107826780125194+c.upper)) = pointBounds36829 := by
 decide +kernel
def cuts36830 : List PrefixCut := [⟨61,324565203,324565405⟩,
⟨64,340411646,340411859⟩]
theorem checked36830 : checkPrefixCuts (2^48) 4831313921 10 Manual.Count131072.C036830.packed 64 cuts36830 = true := by
 decide +kernel
def pointBounds36830 : List (Nat × Nat × Nat) := [(4831438848,107827063785759,107827448665615)]
theorem point_links_checked36830 : (cuts36830.take 1).map (fun c => (4831313921-1+2*2^10*c.k,107826739220556+c.lower,107827124100210+c.upper)) = pointBounds36830 := by
 decide +kernel
def cuts36831 : List PrefixCut := [⟨64,341276255,341276465⟩]
theorem checked36831 : checkPrefixCuts (2^48) 4831444993 10 Manual.Count131072.C036831.packed 64 cuts36831 = true := by
 decide +kernel
def cuts36832 : List PrefixCut := [⟨7,35886484,35886507⟩,
⟨64,346859611,346859823⟩]
theorem checked36832 : checkPrefixCuts (2^48) 4831576065 10 Manual.Count131072.C036832.packed 64 cuts36832 = true := by
 decide +kernel
def pointBounds36832 : List (Nat × Nat × Nat) := [(4831590400,107827456794941,107827841675041)]
theorem point_links_checked36832 : (cuts36832.take 1).map (fun c => (4831576065-1+2*2^10*c.k,107827420908457+c.lower,107827805788534+c.upper)) = pointBounds36832 := by
 decide +kernel
def cuts36833 : List PrefixCut := [⟨17,92917644,92917698⟩,
⟨64,347607594,347607804⟩]
theorem checked36833 : checkPrefixCuts (2^48) 4831707137 10 Manual.Count131072.C036833.packed 64 cuts36833 = true := by
 decide +kernel
def pointBounds36833 : List (Nat × Nat × Nat) := [(4831741952,107827860685712,107828245566055)]
theorem point_links_checked36833 : (cuts36833.take 1).map (fun c => (4831707137-1+2*2^10*c.k,107827767768068+c.lower,107828152648357+c.upper)) = pointBounds36833 := by
 decide +kernel
def cuts36834 : List PrefixCut := [⟨27,142022933,142023023⟩,
⟨64,340258170,340258381⟩]
theorem checked36834 : checkPrefixCuts (2^48) 4831838209 10 Manual.Count131072.C036834.packed 64 cuts36834 = true := by
 decide +kernel
def pointBounds36834 : List (Nat × Nat × Nat) := [(4831893504,107828257398595,107828642279184)]
theorem point_links_checked36834 : (cuts36834.take 1).map (fun c => (4831838209-1+2*2^10*c.k,107828115375662+c.lower,107828500256161+c.upper)) = pointBounds36834 := by
 decide +kernel
def cuts36835 : List PrefixCut := [⟨37,193105930,193106051⟩,
⟨64,339782906,339783116⟩]
theorem checked36835 : checkPrefixCuts (2^48) 4831969281 10 Manual.Count131072.C036835.packed 64 cuts36835 = true := by
 decide +kernel
def pointBounds36835 : List (Nat × Nat × Nat) := [(4832045056,107828648739762,107829033620593)]
theorem point_links_checked36835 : (cuts36835.take 1).map (fun c => (4831969281-1+2*2^10*c.k,107828455633832+c.lower,107828840514542+c.upper)) = pointBounds36835 := by
 decide +kernel
def cuts36836 : List PrefixCut := [⟨47,256185552,256185708⟩,
⟨64,347521042,347521254⟩]
theorem checked36836 : checkPrefixCuts (2^48) 4832100353 10 Manual.Count131072.C036836.packed 64 cuts36836 = true := by
 decide +kernel
def pointBounds36836 : List (Nat × Nat × Nat) := [(4832196608,107829051602290,107829436483366)]
theorem point_links_checked36836 : (cuts36836.take 1).map (fun c => (4832100353-1+2*2^10*c.k,107828795416738+c.lower,107829180297658+c.upper)) = pointBounds36836 := by
 decide +kernel
def cuts36837 : List PrefixCut := [⟨57,299631631,299631811⟩,
⟨64,336211356,336211559⟩]
theorem checked36837 : checkPrefixCuts (2^48) 4832231425 10 Manual.Count131072.C036837.packed 64 cuts36837 = true := by
 decide +kernel
def pointBounds36837 : List (Nat × Nat × Nat) := [(4832348160,107829442569411,107829827450723)]
theorem point_links_checked36837 : (cuts36837.take 1).map (fun c => (4832231425-1+2*2^10*c.k,107829142937780+c.lower,107829527818912+c.upper)) = pointBounds36837 := by
 decide +kernel
def cuts36838 : List PrefixCut := [⟨64,341269724,341269938⟩]
theorem checked36838 : checkPrefixCuts (2^48) 4832362497 10 Manual.Count131072.C036838.packed 64 cuts36838 = true := by
 decide +kernel
def cuts36839 : List PrefixCut := [⟨3,15842985,15842994⟩,
⟨64,344172759,344172972⟩]
theorem checked36839 : checkPrefixCuts (2^48) 4832493569 10 Manual.Count131072.C036839.packed 64 cuts36839 = true := by
 decide +kernel
def pointBounds36839 : List (Nat × Nat × Nat) := [(4832499712,107829836261845,107830221143403)]
theorem point_links_checked36839 : (cuts36839.take 1).map (fun c => (4832493569-1+2*2^10*c.k,107829820418860+c.lower,107830205300409+c.upper)) = pointBounds36839 := by
 decide +kernel
def cuts36840 : List PrefixCut := [⟨13,67563695,67563735⟩,
⟨64,342357856,342358061⟩]
theorem checked36840 : checkPrefixCuts (2^48) 4832624641 10 Manual.Count131072.C036840.packed 64 cuts36840 = true := by
 decide +kernel
def pointBounds36840 : List (Nat × Nat × Nat) := [(4832651264,107830232155314,107830617037116)]
theorem point_links_checked36840 : (cuts36840.take 1).map (fun c => (4832624641-1+2*2^10*c.k,107830164591619+c.lower,107830549473381+c.upper)) = pointBounds36840 := by
 decide +kernel
def cuts36841 : List PrefixCut := [⟨23,126794707,126794783⟩,
⟨64,349861829,349862040⟩]
theorem checked36841 : checkPrefixCuts (2^48) 4832755713 10 Manual.Count131072.C036841.packed 64 cuts36841 = true := by
 decide +kernel
def pointBounds36841 : List (Nat × Nat × Nat) := [(4832802816,107830633744182,107831018626225)]
theorem point_links_checked36841 : (cuts36841.take 1).map (fun c => (4832755713-1+2*2^10*c.k,107830506949475+c.lower,107830891831442+c.upper)) = pointBounds36841 := by
 decide +kernel
def cuts36842 : List PrefixCut := [⟨33,176936649,176936756⟩,
⟨64,342921707,342921912⟩]
theorem checked36842 : checkPrefixCuts (2^48) 4832886785 10 Manual.Count131072.C036842.packed 64 cuts36842 = true := by
 decide +kernel
def pointBounds36842 : List (Nat × Nat × Nat) := [(4832954368,107831033747953,107831418630238)]
theorem point_links_checked36842 : (cuts36842.take 1).map (fun c => (4832886785-1+2*2^10*c.k,107830856811304+c.lower,107831241693482+c.upper)) = pointBounds36842 := by
 decide +kernel
def cuts36843 : List PrefixCut := [⟨43,231152395,231152533⟩,
⟨64,344834265,344834471⟩]
theorem checked36843 : checkPrefixCuts (2^48) 4833017857 10 Manual.Count131072.C036843.packed 64 cuts36843 = true := by
 decide +kernel
def pointBounds36843 : List (Nat × Nat × Nat) := [(4833105920,107831430885406,107831815767927)]
theorem point_links_checked36843 : (cuts36843.take 1).map (fun c => (4833017857-1+2*2^10*c.k,107831199733011+c.lower,107831584615394+c.upper)) = pointBounds36843 := by
 decide +kernel
def cuts36844 : List PrefixCut := [⟨53,282045441,282045613⟩,
⟨64,340107689,340107897⟩]
theorem checked36844 : checkPrefixCuts (2^48) 4833148929 10 Manual.Count131072.C036844.packed 64 cuts36844 = true := by
 decide +kernel
def pointBounds36844 : List (Nat × Nat × Nat) := [(4833257472,107831826612717,107832211495478)]
theorem point_links_checked36844 : (cuts36844.take 1).map (fun c => (4833148929-1+2*2^10*c.k,107831544567276+c.lower,107831929449865+c.upper)) = pointBounds36844 := by
 decide +kernel
def cuts36845 : List PrefixCut := [⟨63,335323152,335323352⟩,
⟨64,340622561,340622764⟩]
theorem checked36845 : checkPrefixCuts (2^48) 4833280001 10 Manual.Count131072.C036845.packed 64 cuts36845 = true := by
 decide +kernel
def pointBounds36845 : List (Nat × Nat × Nat) := [(4833409024,107832219998117,107832604881114)]
theorem point_links_checked36845 : (cuts36845.take 1).map (fun c => (4833280001-1+2*2^10*c.k,107831884674965+c.lower,107832269557762+c.upper)) = pointBounds36845 := by
 decide +kernel
def cuts36846 : List PrefixCut := [⟨64,341370417,341370626⟩]
theorem checked36846 : checkPrefixCuts (2^48) 4833411073 10 Manual.Count131072.C036846.packed 64 cuts36846 = true := by
 decide +kernel
def cuts36847 : List PrefixCut := [⟨9,45829810,45829838⟩,
⟨64,340371153,340371358⟩]
theorem checked36847 : checkPrefixCuts (2^48) 4833542145 10 Manual.Count131072.C036847.packed 64 cuts36847 = true := by
 decide +kernel
def pointBounds36847 : List (Nat × Nat × Nat) := [(4833560576,107832612497753,107832997380990)]
theorem point_links_checked36847 : (cuts36847.take 1).map (fun c => (4833542145-1+2*2^10*c.k,107832566667943+c.lower,107832951551152+c.upper)) = pointBounds36847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000213
