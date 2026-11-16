import PlattAssemblyKernel
import PlattCertificates.Count131072.C030864
import PlattCertificates.Count131072.C030865
import PlattCertificates.Count131072.C030866
import PlattCertificates.Count131072.C030867
import PlattCertificates.Count131072.C030868
import PlattCertificates.Count131072.C030869
import PlattCertificates.Count131072.C030870
import PlattCertificates.Count131072.C030871
import PlattCertificates.Count131072.C030872
import PlattCertificates.Count131072.C030873
import PlattCertificates.Count131072.C030874
import PlattCertificates.Count131072.C030875
import PlattCertificates.Count131072.C030876
import PlattCertificates.Count131072.C030877
import PlattCertificates.Count131072.C030878
import PlattCertificates.Count131072.C030879
import PlattCertificates.Count131072.C030880
import PlattCertificates.Count131072.C030881
import PlattCertificates.Count131072.C030882
import PlattCertificates.Count131072.C030883
import PlattCertificates.Count131072.C030884
import PlattCertificates.Count131072.C030885
import PlattCertificates.Count131072.C030886
import PlattCertificates.Count131072.C030887
import PlattCertificates.Count131072.C030888
import PlattCertificates.Count131072.C030889
import PlattCertificates.Count131072.C030890
import PlattCertificates.Count131072.C030891
import PlattCertificates.Count131072.C030892
import PlattCertificates.Count131072.C030893
import PlattCertificates.Count131072.C030894
import PlattCertificates.Count131072.C030895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30864 : List PrefixCut := [⟨23,79520731,79520774⟩,
⟨128,415114989,415115221⟩]
theorem checked30864 : checkPrefixCuts (2^48) 4049338369 9 Manual.Count131072.C030864.packed 128 cuts30864 = true := by
 decide +kernel
def pointBounds30864 : List (Nat × Nat × Nat) := [(4049361920,105589142081810,105589525606140)]
theorem point_links_checked30864 : (cuts30864.take 1).map (fun c => (4049338369-1+2*2^9*c.k,105589062561079+c.lower,105589446085366+c.upper)) = pointBounds30864 := by
 decide +kernel
def cuts30865 : List PrefixCut := [⟨19,60264226,60264261⟩,
⟨128,412877254,412877486⟩]
theorem checked30865 : checkPrefixCuts (2^48) 4049469441 9 Manual.Count131072.C030865.packed 128 cuts30865 = true := by
 decide +kernel
def pointBounds30865 : List (Nat × Nat × Nat) := [(4049488896,105589537940294,105589921464848)]
theorem point_links_checked30865 : (cuts30865.take 1).map (fun c => (4049469441-1+2*2^9*c.k,105589477676068+c.lower,105589861200587+c.upper)) = pointBounds30865 := by
 decide +kernel
def cuts30866 : List PrefixCut := [⟨15,45526885,45526912⟩,
⟨128,411334720,411334951⟩]
theorem checked30866 : checkPrefixCuts (2^48) 4049600513 9 Manual.Count131072.C030866.packed 128 cuts30866 = true := by
 decide +kernel
def pointBounds30866 : List (Nat × Nat × Nat) := [(4049615872,105589936080207,105590319604985)]
theorem point_links_checked30866 : (cuts30866.take 1).map (fun c => (4049600513-1+2*2^9*c.k,105589890553322+c.lower,105590274078073+c.upper)) = pointBounds30866 := by
 decide +kernel
def cuts30867 : List PrefixCut := [⟨11,35169270,35169291⟩,
⟨128,409861860,409862093⟩]
theorem checked30867 : checkPrefixCuts (2^48) 4049731585 9 Manual.Count131072.C030867.packed 128 cuts30867 = true := by
 decide +kernel
def pointBounds30867 : List (Nat × Nat × Nat) := [(4049742848,105590337057312,105590720582315)]
theorem point_links_checked30867 : (cuts30867.take 1).map (fun c => (4049731585-1+2*2^9*c.k,105590301888042+c.lower,105590685413024+c.upper)) = pointBounds30867 := by
 decide +kernel
def cuts30868 : List PrefixCut := [⟨7,21406699,21406713⟩,
⟨128,416937679,416937911⟩]
theorem checked30868 : checkPrefixCuts (2^48) 4049862657 9 Manual.Count131072.C030868.packed 128 cuts30868 = true := by
 decide +kernel
def pointBounds30868 : List (Nat × Nat × Nat) := [(4049869824,105590733156601,105591116681830)]
theorem point_links_checked30868 : (cuts30868.take 1).map (fun c => (4049862657-1+2*2^9*c.k,105590711749902+c.lower,105591095275117+c.upper)) = pointBounds30868 := by
 decide +kernel
def cuts30869 : List PrefixCut := [⟨3,9243508,9243513⟩,
⟨127,405248516,405248736⟩,
⟨128,408723408,408723630⟩]
theorem checked30869 : checkPrefixCuts (2^48) 4049993729 9 Manual.Count131072.C030869.packed 128 cuts30869 = true := by
 decide +kernel
def pointBounds30869 : List (Nat × Nat × Nat) := [(4049996800,105591137931089,105591521456541),(4050123776,105591533936097,105591917461764)]
theorem point_links_checked30869 : (cuts30869.take 2).map (fun c => (4049993729-1+2*2^9*c.k,105591128687581+c.lower,105591512213028+c.upper)) = pointBounds30869 := by
 decide +kernel
def cuts30870 : List PrefixCut := [⟨123,396617982,396618207⟩,
⟨128,413783402,413783637⟩]
theorem checked30870 : checkPrefixCuts (2^48) 4050124801 9 Manual.Count131072.C030870.packed 128 cuts30870 = true := by
 decide +kernel
def pointBounds30870 : List (Nat × Nat × Nat) := [(4050250752,105591934028971,105592317554865)]
theorem point_links_checked30870 : (cuts30870.take 1).map (fun c => (4050124801-1+2*2^9*c.k,105591537410989+c.lower,105591920936658+c.upper)) = pointBounds30870 := by
 decide +kernel
def cuts30871 : List PrefixCut := [⟨119,383957346,383957566⟩,
⟨128,414256476,414256713⟩]
theorem checked30871 : checkPrefixCuts (2^48) 4050255873 9 Manual.Count131072.C030871.packed 128 cuts30871 = true := by
 decide +kernel
def pointBounds30871 : List (Nat × Nat × Nat) := [(4050377728,105592335151737,105592718677861)]
theorem point_links_checked30871 : (cuts30871.take 1).map (fun c => (4050255873-1+2*2^9*c.k,105591951194391+c.lower,105592334720295+c.upper)) = pointBounds30871 := by
 decide +kernel
def cuts30872 : List PrefixCut := [⟨115,371019473,371019685⟩,
⟨128,413617580,413617816⟩]
theorem checked30872 : checkPrefixCuts (2^48) 4050386945 9 Manual.Count131072.C030872.packed 128 cuts30872 = true := by
 decide +kernel
def pointBounds30872 : List (Nat × Nat × Nat) := [(4050504704,105592736470340,105593119996693)]
theorem point_links_checked30872 : (cuts30872.take 1).map (fun c => (4050386945-1+2*2^9*c.k,105592365450867+c.lower,105592748977008+c.upper)) = pointBounds30872 := by
 decide +kernel
def cuts30873 : List PrefixCut := [⟨111,352662362,352662559⟩,
⟨128,408114575,408114801⟩]
theorem checked30873 : checkPrefixCuts (2^48) 4050518017 9 Manual.Count131072.C030873.packed 128 cuts30873 = true := by
 decide +kernel
def pointBounds30873 : List (Nat × Nat × Nat) := [(4050631680,105593131730809,105593515257383)]
theorem point_links_checked30873 : (cuts30873.take 1).map (fun c => (4050518017-1+2*2^9*c.k,105592779068447+c.lower,105593162594824+c.upper)) = pointBounds30873 := by
 decide +kernel
def cuts30874 : List PrefixCut := [⟨107,345771778,345771975⟩,
⟨128,414355223,414355459⟩]
theorem checked30874 : checkPrefixCuts (2^48) 4050649089 9 Manual.Count131072.C030874.packed 128 cuts30874 = true := by
 decide +kernel
def pointBounds30874 : List (Nat × Nat × Nat) := [(4050758656,105593532954800,105593916481600)]
theorem point_links_checked30874 : (cuts30874.take 1).map (fun c => (4050649089-1+2*2^9*c.k,105593187183022+c.lower,105593570709625+c.upper)) = pointBounds30874 := by
 decide +kernel
def cuts30875 : List PrefixCut := [⟨103,331585707,331585889⟩,
⟨128,412257283,412257511⟩]
theorem checked30875 : checkPrefixCuts (2^48) 4050780161 9 Manual.Count131072.C030875.packed 128 cuts30875 = true := by
 decide +kernel
def pointBounds30875 : List (Nat × Nat × Nat) := [(4050885632,105593933123952,105594316650973)]
theorem point_links_checked30875 : (cuts30875.take 1).map (fun c => (4050780161-1+2*2^9*c.k,105593601538245+c.lower,105593985065084+c.upper)) = pointBounds30875 := by
 decide +kernel
def cuts30876 : List PrefixCut := [⟨99,316427713,316427897⟩,
⟨128,408700270,408700506⟩]
theorem checked30876 : checkPrefixCuts (2^48) 4050911233 9 Manual.Count131072.C030876.packed 128 cuts30876 = true := by
 decide +kernel
def pointBounds30876 : List (Nat × Nat × Nat) := [(4051012608,105594330223241,105594713750492)]
theorem point_links_checked30876 : (cuts30876.take 1).map (fun c => (4050911233-1+2*2^9*c.k,105594013795528+c.lower,105594397322595+c.upper)) = pointBounds30876 := by
 decide +kernel
def cuts30877 : List PrefixCut := [⟨95,306481806,306481978⟩,
⟨128,411188370,411188600⟩]
theorem checked30877 : checkPrefixCuts (2^48) 4051042305 9 Manual.Count131072.C030877.packed 128 cuts30877 = true := by
 decide +kernel
def pointBounds30877 : List (Nat × Nat × Nat) := [(4051139584,105594728977604,105595112505079)]
theorem point_links_checked30877 : (cuts30877.take 1).map (fun c => (4051042305-1+2*2^9*c.k,105594422495798+c.lower,105594806023101+c.upper)) = pointBounds30877 := by
 decide +kernel
def cuts30878 : List PrefixCut := [⟨91,293271085,293271251⟩,
⟨128,411869908,411870138⟩]
theorem checked30878 : checkPrefixCuts (2^48) 4051173377 9 Manual.Count131072.C030878.packed 128 cuts30878 = true := by
 decide +kernel
def pointBounds30878 : List (Nat × Nat × Nat) := [(4051266560,105595126955253,105595510482952)]
theorem point_links_checked30878 : (cuts30878.take 1).map (fun c => (4051173377-1+2*2^9*c.k,105594833684168+c.lower,105595217211701+c.upper)) = pointBounds30878 := by
 decide +kernel
def cuts30879 : List PrefixCut := [⟨87,274711416,274711573⟩,
⟨128,408521628,408521862⟩]
theorem checked30879 : checkPrefixCuts (2^48) 4051304449 9 Manual.Count131072.C030879.packed 128 cuts30879 = true := by
 decide +kernel
def pointBounds30879 : List (Nat × Nat × Nat) := [(4051393536,105595520265492,105595903793412)]
theorem point_links_checked30879 : (cuts30879.take 1).map (fun c => (4051304449-1+2*2^9*c.k,105595245554076+c.lower,105595629081839+c.upper)) = pointBounds30879 := by
 decide +kernel
def cuts30880 : List PrefixCut := [⟨83,267407819,267407970⟩,
⟨128,410662158,410662391⟩]
theorem checked30880 : checkPrefixCuts (2^48) 4051435521 9 Manual.Count131072.C030880.packed 128 cuts30880 = true := by
 decide +kernel
def pointBounds30880 : List (Nat × Nat × Nat) := [(4051520512,105595921483523,105596305011671)]
theorem point_links_checked30880 : (cuts30880.take 1).map (fun c => (4051435521-1+2*2^9*c.k,105595654075704+c.lower,105596037603701+c.upper)) = pointBounds30880 := by
 decide +kernel
def cuts30881 : List PrefixCut := [⟨79,252462741,252462878⟩,
⟨128,411968818,411969043⟩]
theorem checked30881 : checkPrefixCuts (2^48) 4051566593 9 Manual.Count131072.C030881.packed 128 cuts30881 = true := by
 decide +kernel
def pointBounds30881 : List (Nat × Nat × Nat) := [(4051647488,105596317200603,105596700728970)]
theorem point_links_checked30881 : (cuts30881.take 1).map (fun c => (4051566593-1+2*2^9*c.k,105596064737862+c.lower,105596448266092+c.upper)) = pointBounds30881 := by
 decide +kernel
def cuts30882 : List PrefixCut := [⟨75,243840394,243840532⟩,
⟨128,411608178,411608408⟩]
theorem checked30882 : checkPrefixCuts (2^48) 4051697665 9 Manual.Count131072.C030882.packed 128 cuts30882 = true := by
 decide +kernel
def pointBounds30882 : List (Nat × Nat × Nat) := [(4051774464,105596720547074,105597104075667)]
theorem point_links_checked30882 : (cuts30882.take 1).map (fun c => (4051697665-1+2*2^9*c.k,105596476706680+c.lower,105596860235135+c.upper)) = pointBounds30882 := by
 decide +kernel
def cuts30883 : List PrefixCut := [⟨71,226048834,226048962⟩,
⟨128,411455887,411456119⟩]
theorem checked30883 : checkPrefixCuts (2^48) 4051828737 9 Manual.Count131072.C030883.packed 128 cuts30883 = true := by
 decide +kernel
def pointBounds30883 : List (Nat × Nat × Nat) := [(4051901440,105597114363692,105597497892505)]
theorem point_links_checked30883 : (cuts30883.take 1).map (fun c => (4051828737-1+2*2^9*c.k,105596888314858+c.lower,105597271843543+c.upper)) = pointBounds30883 := by
 decide +kernel
def cuts30884 : List PrefixCut := [⟨67,217566789,217566911⟩,
⟨128,407552610,407552843⟩]
theorem checked30884 : checkPrefixCuts (2^48) 4051959809 9 Manual.Count131072.C030884.packed 128 cuts30884 = true := by
 decide +kernel
def pointBounds30884 : List (Nat × Nat × Nat) := [(4052028416,105597517337534,105597900866573)]
theorem point_links_checked30884 : (cuts30884.take 1).map (fun c => (4051959809-1+2*2^9*c.k,105597299770745+c.lower,105597683299662+c.upper)) = pointBounds30884 := by
 decide +kernel
def cuts30885 : List PrefixCut := [⟨63,207557113,207557227⟩,
⟨128,415110882,415111112⟩]
theorem checked30885 : checkPrefixCuts (2^48) 4052090881 9 Manual.Count131072.C030885.packed 128 cuts30885 = true := by
 decide +kernel
def pointBounds30885 : List (Nat × Nat × Nat) := [(4052155392,105597914880468,105598298409732)]
theorem point_links_checked30885 : (cuts30885.take 1).map (fun c => (4052090881-1+2*2^9*c.k,105597707323355+c.lower,105598090852505+c.upper)) = pointBounds30885 := by
 decide +kernel
def cuts30886 : List PrefixCut := [⟨59,189073796,189073896⟩,
⟨128,411624376,411624598⟩]
theorem checked30886 : checkPrefixCuts (2^48) 4052221953 9 Manual.Count131072.C030886.packed 128 cuts30886 = true := by
 decide +kernel
def pointBounds30886 : List (Nat × Nat × Nat) := [(4052282368,105598311508033,105598695037513)]
theorem point_links_checked30886 : (cuts30886.take 1).map (fun c => (4052221953-1+2*2^9*c.k,105598122434237+c.lower,105598505963617+c.upper)) = pointBounds30886 := by
 decide +kernel
def cuts30887 : List PrefixCut := [⟨55,176009450,176009550⟩,
⟨128,411541589,411541825⟩]
theorem checked30887 : checkPrefixCuts (2^48) 4052353025 9 Manual.Count131072.C030887.packed 128 cuts30887 = true := by
 decide +kernel
def pointBounds30887 : List (Nat × Nat × Nat) := [(4052409344,105598710068063,105599093597765)]
theorem point_links_checked30887 : (cuts30887.take 1).map (fun c => (4052353025-1+2*2^9*c.k,105598534058613+c.lower,105598917588215+c.upper)) = pointBounds30887 := by
 decide +kernel
def cuts30888 : List PrefixCut := [⟨51,166627166,166627261⟩,
⟨128,412570170,412570401⟩]
theorem checked30888 : checkPrefixCuts (2^48) 4052484097 9 Manual.Count131072.C030888.packed 128 cuts30888 = true := by
 decide +kernel
def pointBounds30888 : List (Nat × Nat × Nat) := [(4052536320,105599112227368,105599495757301)]
theorem point_links_checked30888 : (cuts30888.take 1).map (fun c => (4052484097-1+2*2^9*c.k,105598945600202+c.lower,105599329130040+c.upper)) = pointBounds30888 := by
 decide +kernel
def cuts30889 : List PrefixCut := [⟨47,154397832,154397918⟩,
⟨128,412626271,412626504⟩]
theorem checked30889 : checkPrefixCuts (2^48) 4052615169 9 Manual.Count131072.C030889.packed 128 cuts30889 = true := by
 decide +kernel
def pointBounds30889 : List (Nat × Nat × Nat) := [(4052663296,105599512568204,105599896098359)]
theorem point_links_checked30889 : (cuts30889.take 1).map (fun c => (4052615169-1+2*2^9*c.k,105599358170372+c.lower,105599741700441+c.upper)) = pointBounds30889 := by
 decide +kernel
def cuts30890 : List PrefixCut := [⟨43,140849682,140849762⟩,
⟨128,414210297,414210522⟩]
theorem checked30890 : checkPrefixCuts (2^48) 4052746241 9 Manual.Count131072.C030890.packed 128 cuts30890 = true := by
 decide +kernel
def pointBounds30890 : List (Nat × Nat × Nat) := [(4052790272,105599911646325,105600295176707)]
theorem point_links_checked30890 : (cuts30890.take 1).map (fun c => (4052746241-1+2*2^9*c.k,105599770796643+c.lower,105600154326945+c.upper)) = pointBounds30890 := by
 decide +kernel
def cuts30891 : List PrefixCut := [⟨39,123760420,123760493⟩,
⟨128,409752112,409752346⟩]
theorem checked30891 : checkPrefixCuts (2^48) 4052877313 9 Manual.Count131072.C030891.packed 128 cuts30891 = true := by
 decide +kernel
def pointBounds30891 : List (Nat × Nat × Nat) := [(4052917248,105600308767360,105600692297960)]
theorem point_links_checked30891 : (cuts30891.take 1).map (fun c => (4052877313-1+2*2^9*c.k,105600185006940+c.lower,105600568537467+c.upper)) = pointBounds30891 := by
 decide +kernel
def cuts30892 : List PrefixCut := [⟨35,111186376,111186440⟩,
⟨128,409322189,409322418⟩]
theorem checked30892 : checkPrefixCuts (2^48) 4053008385 9 Manual.Count131072.C030892.packed 128 cuts30892 = true := by
 decide +kernel
def pointBounds30892 : List (Nat × Nat × Nat) := [(4053044224,105600705945428,105601089476253)]
theorem point_links_checked30892 : (cuts30892.take 1).map (fun c => (4053008385-1+2*2^9*c.k,105600594759052+c.lower,105600978289813+c.upper)) = pointBounds30892 := by
 decide +kernel
def cuts30893 : List PrefixCut := [⟨31,101668753,101668811⟩,
⟨128,414170089,414170321⟩]
theorem checked30893 : checkPrefixCuts (2^48) 4053139457 9 Manual.Count131072.C030893.packed 128 cuts30893 = true := by
 decide +kernel
def pointBounds30893 : List (Nat × Nat × Nat) := [(4053171200,105601105749994,105601489281042)]
theorem point_links_checked30893 : (cuts30893.take 1).map (fun c => (4053139457-1+2*2^9*c.k,105601004081241+c.lower,105601387612231+c.upper)) = pointBounds30893 := by
 decide +kernel
def cuts30894 : List PrefixCut := [⟨27,86665685,86665734⟩,
⟨128,412420631,412420864⟩]
theorem checked30894 : checkPrefixCuts (2^48) 4053270529 9 Manual.Count131072.C030894.packed 128 cuts30894 = true := by
 decide +kernel
def pointBounds30894 : List (Nat × Nat × Nat) := [(4053298176,105601504917015,105601888448286)]
theorem point_links_checked30894 : (cuts30894.take 1).map (fun c => (4053270529-1+2*2^9*c.k,105601418251330+c.lower,105601801782552+c.upper)) = pointBounds30894 := by
 decide +kernel
def cuts30895 : List PrefixCut := [⟨23,74441238,74441283⟩,
⟨128,414837656,414837885⟩]
theorem checked30895 : checkPrefixCuts (2^48) 4053401601 9 Manual.Count131072.C030895.packed 128 cuts30895 = true := by
 decide +kernel
def pointBounds30895 : List (Nat × Nat × Nat) := [(4053425152,105601905113199,105602288644699)]
theorem point_links_checked30895 : (cuts30895.take 1).map (fun c => (4053401601-1+2*2^9*c.k,105601830671961+c.lower,105602214203416+c.upper)) = pointBounds30895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000027
