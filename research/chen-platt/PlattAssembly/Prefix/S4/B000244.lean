import PlattAssemblyKernel
import PlattCertificates.Count131072.C037808
import PlattCertificates.Count131072.C037809
import PlattCertificates.Count131072.C037810
import PlattCertificates.Count131072.C037811
import PlattCertificates.Count131072.C037812
import PlattCertificates.Count131072.C037813
import PlattCertificates.Count131072.C037814
import PlattCertificates.Count131072.C037815
import PlattCertificates.Count131072.C037816
import PlattCertificates.Count131072.C037817
import PlattCertificates.Count131072.C037818
import PlattCertificates.Count131072.C037819
import PlattCertificates.Count131072.C037820
import PlattCertificates.Count131072.C037821
import PlattCertificates.Count131072.C037822
import PlattCertificates.Count131072.C037823
import PlattCertificates.Count131072.C037824
import PlattCertificates.Count131072.C037825
import PlattCertificates.Count131072.C037826
import PlattCertificates.Count131072.C037827
import PlattCertificates.Count131072.C037828
import PlattCertificates.Count131072.C037829
import PlattCertificates.Count131072.C037830
import PlattCertificates.Count131072.C037831
import PlattCertificates.Count131072.C037832
import PlattCertificates.Count131072.C037833
import PlattCertificates.Count131072.C037834
import PlattCertificates.Count131072.C037835
import PlattCertificates.Count131072.C037836
import PlattCertificates.Count131072.C037837
import PlattCertificates.Count131072.C037838
import PlattCertificates.Count131072.C037839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts37808 : List PrefixCut := [⟨32,167198139,167198239⟩,
⟨64,333883289,333883492⟩]
theorem checked37808 : checkPrefixCuts (2^48) 4959502337 10 Manual.Count131072.C037808.packed 64 cuts37808 = true := by
 decide +kernel
def pointBounds37808 : List (Nat × Nat × Nat) := [(4959567872,108157272664234,108157657744993)]
theorem point_links_checked37808 : (cuts37808.take 1).map (fun c => (4959502337-1+2*2^10*c.k,108157105466095+c.lower,108157490546754+c.upper)) = pointBounds37808 := by
 decide +kernel
def cuts37809 : List PrefixCut := [⟨44,231323793,231323931⟩,
⟨64,336485055,336485257⟩]
theorem checked37809 : checkPrefixCuts (2^48) 4959633409 10 Manual.Count131072.C037809.packed 64 cuts37809 = true := by
 decide +kernel
def pointBounds37809 : List (Nat × Nat × Nat) := [(4959723520,108157670673177,108158055754177)]
theorem point_links_checked37809 : (cuts37809.take 1).map (fun c => (4959633409-1+2*2^10*c.k,108157439349384+c.lower,108157824430246+c.upper)) = pointBounds37809 := by
 decide +kernel
def cuts37810 : List PrefixCut := [⟨56,293913426,293913601⟩,
⟨64,334943863,334944063⟩]
theorem checked37810 : checkPrefixCuts (2^48) 4959764481 10 Manual.Count131072.C037810.packed 64 cuts37810 = true := by
 decide +kernel
def pointBounds37810 : List (Nat × Nat × Nat) := [(4959879168,108158069747865,108158454829104)]
theorem point_links_checked37810 : (cuts37810.take 1).map (fun c => (4959764481-1+2*2^10*c.k,108157775834439+c.lower,108158160915503+c.upper)) = pointBounds37810 := by
 decide +kernel
def cuts37811 : List PrefixCut := [⟨64,333232568,333232772⟩]
theorem checked37811 : checkPrefixCuts (2^48) 4959895553 10 Manual.Count131072.C037811.packed 64 cuts37811 = true := by
 decide +kernel
def cuts37812 : List PrefixCut := [⟨4,21337481,21337494⟩,
⟨64,332769798,332770001⟩]
theorem checked37812 : checkPrefixCuts (2^48) 4960026625 10 Manual.Count131072.C037812.packed 64 cuts37812 = true := by
 decide +kernel
def pointBounds37812 : List (Nat × Nat × Nat) := [(4960034816,108158465348351,108158850429832)]
theorem point_links_checked37812 : (cuts37812.take 1).map (fun c => (4960026625-1+2*2^10*c.k,108158444010870+c.lower,108158829092338+c.upper)) = pointBounds37812 := by
 decide +kernel
def cuts37813 : List PrefixCut := [⟨16,81999380,81999430⟩,
⟨64,332533990,332534193⟩]
theorem checked37813 : checkPrefixCuts (2^48) 4960157697 10 Manual.Count131072.C037813.packed 64 cuts37813 = true := by
 decide +kernel
def pointBounds37813 : List (Nat × Nat × Nat) := [(4960190464,108158858780048,108159243861769)]
theorem point_links_checked37813 : (cuts37813.take 1).map (fun c => (4960157697-1+2*2^10*c.k,108158776780668+c.lower,108159161862339+c.upper)) = pointBounds37813 := by
 decide +kernel
def cuts37814 : List PrefixCut := [⟨28,143281974,143282064⟩,
⟨64,331106562,331106766⟩]
theorem checked37814 : checkPrefixCuts (2^48) 4960288769 10 Manual.Count131072.C037814.packed 64 cuts37814 = true := by
 decide +kernel
def pointBounds37814 : List (Nat × Nat × Nat) := [(4960346112,108159252596632,108159637678596)]
theorem point_links_checked37814 : (cuts37814.take 1).map (fun c => (4960288769-1+2*2^10*c.k,108159109314658+c.lower,108159494396532+c.upper)) = pointBounds37814 := by
 decide +kernel
def cuts37815 : List PrefixCut := [⟨40,209100531,209100659⟩,
⟨64,335069881,335070088⟩]
theorem checked37815 : checkPrefixCuts (2^48) 4960419841 10 Manual.Count131072.C037815.packed 64 cuts37815 = true := by
 decide +kernel
def pointBounds37815 : List (Nat × Nat × Nat) := [(4960501760,108159649521751,108160034603957)]
theorem point_links_checked37815 : (cuts37815.take 1).map (fun c => (4960419841-1+2*2^10*c.k,108159440421220+c.lower,108159825503298+c.upper)) = pointBounds37815 := by
 decide +kernel
def cuts37816 : List PrefixCut := [⟨52,272532097,272532263⟩,
⟨64,334834054,334834260⟩]
theorem checked37816 : checkPrefixCuts (2^48) 4960550913 10 Manual.Count131072.C037816.packed 64 cuts37816 = true := by
 decide +kernel
def pointBounds37816 : List (Nat × Nat × Nat) := [(4960657408,108160048023198,108160433105649)]
theorem point_links_checked37816 : (cuts37816.take 1).map (fun c => (4960550913-1+2*2^10*c.k,108159775491101+c.lower,108160160573386+c.upper)) = pointBounds37816 := by
 decide +kernel
def cuts37817 : List PrefixCut := [⟨64,333520132,333520334⟩]
theorem checked37817 : checkPrefixCuts (2^48) 4960681985 10 Manual.Count131072.C037817.packed 64 cuts37817 = true := by
 decide +kernel
def pointBounds37817 : List (Nat × Nat × Nat) := [(4960813056,108160443845287,108160828927980)]
theorem point_links_checked37817 : (cuts37817.take 1).map (fun c => (4960681985-1+2*2^10*c.k,108160110325155+c.lower,108160495407646+c.upper)) = pointBounds37817 := by
 decide +kernel
def cuts37818 : List PrefixCut := [⟨64,335724167,335724369⟩]
theorem checked37818 : checkPrefixCuts (2^48) 4960813057 10 Manual.Count131072.C037818.packed 64 cuts37818 = true := by
 decide +kernel
def cuts37819 : List PrefixCut := [⟨12,61787711,61787750⟩,
⟨64,334750768,334750969⟩]
theorem checked37819 : checkPrefixCuts (2^48) 4960944129 10 Manual.Count131072.C037819.packed 64 cuts37819 = true := by
 decide +kernel
def pointBounds37819 : List (Nat × Nat × Nat) := [(4960968704,108160841357165,108161226440099)]
theorem point_links_checked37819 : (cuts37819.take 1).map (fun c => (4960944129-1+2*2^10*c.k,108160779569454+c.lower,108161164652349+c.upper)) = pointBounds37819 := by
 decide +kernel
def cuts37820 : List PrefixCut := [⟨24,125500886,125500961⟩,
⟨64,335763177,335763377⟩]
theorem checked37820 : checkPrefixCuts (2^48) 4961075201 10 Manual.Count131072.C037820.packed 64 cuts37820 = true := by
 decide +kernel
def pointBounds37820 : List (Nat × Nat × Nat) := [(4961124352,108161239821108,108161624904279)]
theorem point_links_checked37820 : (cuts37820.take 1).map (fun c => (4961075201-1+2*2^10*c.k,108161114320222+c.lower,108161499403318+c.upper)) = pointBounds37820 := by
 decide +kernel
def cuts37821 : List PrefixCut := [⟨36,186089980,186090094⟩,
⟨64,332236773,332236974⟩]
theorem checked37821 : checkPrefixCuts (2^48) 4961206273 10 Manual.Count131072.C037821.packed 64 cuts37821 = true := by
 decide +kernel
def pointBounds37821 : List (Nat × Nat × Nat) := [(4961280000,108161636173379,108162021256789)]
theorem point_links_checked37821 : (cuts37821.take 1).map (fun c => (4961206273-1+2*2^10*c.k,108161450083399+c.lower,108161835166695+c.upper)) = pointBounds37821 := by
 decide +kernel
def cuts37822 : List PrefixCut := [⟨48,248150635,248150788⟩,
⟨64,332057800,332058002⟩]
theorem checked37822 : checkPrefixCuts (2^48) 4961337345 10 Manual.Count131072.C037822.packed 64 cuts37822 = true := by
 decide +kernel
def pointBounds37822 : List (Nat × Nat × Nat) := [(4961435648,108162030470807,108162415554457)]
theorem point_links_checked37822 : (cuts37822.take 1).map (fun c => (4961337345-1+2*2^10*c.k,108161782320172+c.lower,108162167403669+c.upper)) = pointBounds37822 := by
 decide +kernel
def cuts37823 : List PrefixCut := [⟨60,314916403,314916596⟩,
⟨64,335509656,335509861⟩]
theorem checked37823 : checkPrefixCuts (2^48) 4961468417 10 Manual.Count131072.C037823.packed 64 cuts37823 = true := by
 decide +kernel
def pointBounds37823 : List (Nat × Nat × Nat) := [(4961591296,108162429294375,108162814378267)]
theorem point_links_checked37823 : (cuts37823.take 1).map (fun c => (4961468417-1+2*2^10*c.k,108162114377972+c.lower,108162499461671+c.upper)) = pointBounds37823 := by
 decide +kernel
def cuts37824 : List PrefixCut := [⟨64,329714344,329714546⟩]
theorem checked37824 : checkPrefixCuts (2^48) 4961599489 10 Manual.Count131072.C037824.packed 64 cuts37824 = true := by
 decide +kernel
def cuts37825 : List PrefixCut := [⟨8,40788210,40788236⟩,
⟨64,330216159,330216361⟩]
theorem checked37825 : checkPrefixCuts (2^48) 4961730561 10 Manual.Count131072.C037825.packed 64 cuts37825 = true := by
 decide +kernel
def pointBounds37825 : List (Nat × Nat × Nat) := [(4961746944,108162820390182,108163205474314)]
theorem point_links_checked37825 : (cuts37825.take 1).map (fun c => (4961730561-1+2*2^10*c.k,108162779601972+c.lower,108163164686078+c.upper)) = pointBounds37825 := by
 decide +kernel
def cuts37826 : List PrefixCut := [⟨20,105513043,105513105⟩,
⟨64,334972529,334972730⟩]
theorem checked37826 : checkPrefixCuts (2^48) 4961861633 10 Manual.Count131072.C037826.packed 64 cuts37826 = true := by
 decide +kernel
def pointBounds37826 : List (Nat × Nat × Nat) := [(4961902592,108163215331174,108163600415544)]
theorem point_links_checked37826 : (cuts37826.take 1).map (fun c => (4961861633-1+2*2^10*c.k,108163109818131+c.lower,108163494902439+c.upper)) = pointBounds37826 := by
 decide +kernel
def cuts37827 : List PrefixCut := [⟨32,169837060,169837164⟩,
⟨64,336665457,336665661⟩]
theorem checked37827 : checkPrefixCuts (2^48) 4961992705 10 Manual.Count131072.C037827.packed 64 cuts37827 = true := by
 decide +kernel
def pointBounds37827 : List (Nat × Nat × Nat) := [(4962058240,108163614627720,108163999712333)]
theorem point_links_checked37827 : (cuts37827.take 1).map (fun c => (4961992705-1+2*2^10*c.k,108163444790660+c.lower,108163829875169+c.upper)) = pointBounds37827 := by
 decide +kernel
def cuts37828 : List PrefixCut := [⟨44,228541670,228541809⟩,
⟨64,331608120,331608319⟩]
theorem checked37828 : checkPrefixCuts (2^48) 4962123777 10 Manual.Count131072.C037828.packed 64 cuts37828 = true := by
 decide +kernel
def pointBounds37828 : List (Nat × Nat × Nat) := [(4962213888,108164009997787,108164395082639)]
theorem point_links_checked37828 : (cuts37828.take 1).map (fun c => (4962123777-1+2*2^10*c.k,108163781456117+c.lower,108164166540830+c.upper)) = pointBounds37828 := by
 decide +kernel
def cuts37829 : List PrefixCut := [⟨56,292064273,292064449⟩,
⟨64,332336735,332336934⟩]
theorem checked37829 : checkPrefixCuts (2^48) 4962254849 10 Manual.Count131072.C037829.packed 64 cuts37829 = true := by
 decide +kernel
def pointBounds37829 : List (Nat × Nat × Nat) := [(4962369536,108164405128510,108164790213598)]
theorem point_links_checked37829 : (cuts37829.take 1).map (fun c => (4962254849-1+2*2^10*c.k,108164113064237+c.lower,108164498149149+c.upper)) = pointBounds37829 := by
 decide +kernel
def cuts37830 : List PrefixCut := [⟨64,332271260,332271461⟩]
theorem checked37830 : checkPrefixCuts (2^48) 4962385921 10 Manual.Count131072.C037830.packed 64 cuts37830 = true := by
 decide +kernel
def cuts37831 : List PrefixCut := [⟨4,20589411,20589423⟩,
⟨64,327271163,327271359⟩]
theorem checked37831 : checkPrefixCuts (2^48) 4962516993 10 Manual.Count131072.C037831.packed 64 cuts37831 = true := by
 decide +kernel
def pointBounds37831 : List (Nat × Nat × Nat) := [(4962525184,108164798261643,108165183346967)]
theorem point_links_checked37831 : (cuts37831.take 1).map (fun c => (4962516993-1+2*2^10*c.k,108164777672232+c.lower,108165162757544+c.upper)) = pointBounds37831 := by
 decide +kernel
def cuts37832 : List PrefixCut := [⟨16,83546352,83546401⟩,
⟨64,333274608,333274807⟩]
theorem checked37832 : checkPrefixCuts (2^48) 4962648065 10 Manual.Count131072.C037832.packed 64 cuts37832 = true := by
 decide +kernel
def pointBounds37832 : List (Nat × Nat × Nat) := [(4962680832,108165188489747,108165573575304)]
theorem point_links_checked37832 : (cuts37832.take 1).map (fun c => (4962648065-1+2*2^10*c.k,108165104943395+c.lower,108165490028903+c.upper)) = pointBounds37832 := by
 decide +kernel
def cuts37833 : List PrefixCut := [⟨28,146216066,146216155⟩,
⟨64,331961341,331961544⟩]
theorem checked37833 : checkPrefixCuts (2^48) 4962779137 10 Manual.Count131072.C037833.packed 64 cuts37833 = true := by
 decide +kernel
def pointBounds37833 : List (Nat × Nat × Nat) := [(4962836480,108165584434069,108165969519865)]
theorem point_links_checked37833 : (cuts37833.take 1).map (fun c => (4962779137-1+2*2^10*c.k,108165438218003+c.lower,108165823303710+c.upper)) = pointBounds37833 := by
 decide +kernel
def cuts37834 : List PrefixCut := [⟨40,203324091,203324217⟩,
⟨64,329457081,329457281⟩]
theorem checked37834 : checkPrefixCuts (2^48) 4962910209 10 Manual.Count131072.C037834.packed 64 cuts37834 = true := by
 decide +kernel
def pointBounds37834 : List (Nat × Nat × Nat) := [(4962992128,108165973503435,108166358589471)]
theorem point_links_checked37834 : (cuts37834.take 1).map (fun c => (4962910209-1+2*2^10*c.k,108165770179344+c.lower,108166155265254+c.upper)) = pointBounds37834 := by
 decide +kernel
def cuts37835 : List PrefixCut := [⟨52,272168523,272168685⟩,
⟨64,336254032,336254233⟩]
theorem checked37835 : checkPrefixCuts (2^48) 4963041281 10 Manual.Count131072.C037835.packed 64 cuts37835 = true := by
 decide +kernel
def pointBounds37835 : List (Nat × Nat × Nat) := [(4963147776,108166371804948,108166756891220)]
theorem point_links_checked37835 : (cuts37835.take 1).map (fun c => (4963041281-1+2*2^10*c.k,108166099636425+c.lower,108166484722535+c.upper)) = pointBounds37835 := by
 decide +kernel
def cuts37836 : List PrefixCut := [⟨64,331481294,331481496⟩]
theorem checked37836 : checkPrefixCuts (2^48) 4963172353 10 Manual.Count131072.C037836.packed 64 cuts37836 = true := by
 decide +kernel
def pointBounds37836 : List (Nat × Nat × Nat) := [(4963303424,108166767371751,108167152458264)]
theorem point_links_checked37836 : (cuts37836.take 1).map (fun c => (4963172353-1+2*2^10*c.k,108166435890457+c.lower,108166820976768+c.upper)) = pointBounds37836 := by
 decide +kernel
def cuts37837 : List PrefixCut := [⟨64,336633249,336633451⟩]
theorem checked37837 : checkPrefixCuts (2^48) 4963303425 10 Manual.Count131072.C037837.packed 64 cuts37837 = true := by
 decide +kernel
def cuts37838 : List PrefixCut := [⟨12,62607356,62607394⟩,
⟨64,330046129,330046333⟩]
theorem checked37838 : checkPrefixCuts (2^48) 4963434497 10 Manual.Count131072.C037838.packed 64 cuts37838 = true := by
 decide +kernel
def pointBounds37838 : List (Nat × Nat × Nat) := [(4963459072,108167166612356,108167551699109)]
theorem point_links_checked37838 : (cuts37838.take 1).map (fun c => (4963434497-1+2*2^10*c.k,108167104005000+c.lower,108167489091715+c.upper)) = pointBounds37838 := by
 decide +kernel
def cuts37839 : List PrefixCut := [⟨24,126345258,126345336⟩,
⟨64,332986224,332986427⟩]
theorem checked37839 : checkPrefixCuts (2^48) 4963565569 10 Manual.Count131072.C037839.packed 64 cuts37839 = true := by
 decide +kernel
def pointBounds37839 : List (Nat × Nat × Nat) := [(4963614720,108167560396387,108167945483384)]
theorem point_links_checked37839 : (cuts37839.take 1).map (fun c => (4963565569-1+2*2^10*c.k,108167434051129+c.lower,108167819138048+c.upper)) = pointBounds37839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000244
