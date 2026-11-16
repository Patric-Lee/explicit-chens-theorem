import PlattAssemblyKernel
import PlattCertificates.Count131072.C019888
import PlattCertificates.Count131072.C019889
import PlattCertificates.Count131072.C019890
import PlattCertificates.Count131072.C019891
import PlattCertificates.Count131072.C019892
import PlattCertificates.Count131072.C019893
import PlattCertificates.Count131072.C019894
import PlattCertificates.Count131072.C019895
import PlattCertificates.Count131072.C019896
import PlattCertificates.Count131072.C019897
import PlattCertificates.Count131072.C019898
import PlattCertificates.Count131072.C019899
import PlattCertificates.Count131072.C019900
import PlattCertificates.Count131072.C019901
import PlattCertificates.Count131072.C019902
import PlattCertificates.Count131072.C019903
import PlattCertificates.Count131072.C019904
import PlattCertificates.Count131072.C019905
import PlattCertificates.Count131072.C019906
import PlattCertificates.Count131072.C019907
import PlattCertificates.Count131072.C019908
import PlattCertificates.Count131072.C019909
import PlattCertificates.Count131072.C019910
import PlattCertificates.Count131072.C019911
import PlattCertificates.Count131072.C019912
import PlattCertificates.Count131072.C019913
import PlattCertificates.Count131072.C019914
import PlattCertificates.Count131072.C019915
import PlattCertificates.Count131072.C019916
import PlattCertificates.Count131072.C019917
import PlattCertificates.Count131072.C019918
import PlattCertificates.Count131072.C019919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000309
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19888 : List PrefixCut := [⟨61,314388246,314388432⟩,
⟨128,657770112,657770497⟩]
theorem checked19888 : checkPrefixCuts (2^48) 2610692097 9 Manual.Count131072.C019888.packed 128 cuts19888 = true := by
 decide +kernel
def pointBounds19888 : List (Nat × Nat × Nat) := [(2610754560,99948400540521,99948780867695)]
theorem point_links_checked19888 : (cuts19888.take 1).map (fun c => (2610692097-1+2*2^9*c.k,99948086152275+c.lower,99948466479263+c.upper)) = pointBounds19888 := by
 decide +kernel
def cuts19889 : List PrefixCut := [⟨13,63284770,63284810⟩,
⟨93,470046468,470046744⟩,
⟨128,647387524,647387904⟩]
theorem checked19889 : checkPrefixCuts (2^48) 2610823169 9 Manual.Count131072.C019889.packed 128 cuts19889 = true := by
 decide +kernel
def pointBounds19889 : List (Nat × Nat × Nat) := [(2610836480,99948807207157,99949187534570),(2610918400,99949213968855,99949594296504)]
theorem point_links_checked19889 : (cuts19889.take 2).map (fun c => (2610823169-1+2*2^9*c.k,99948743922387+c.lower,99949124249760+c.upper)) = pointBounds19889 := by
 decide +kernel
def cuts19890 : List PrefixCut := [⟨45,227251732,227251867⟩,
⟨125,637221862,637222236⟩,
⟨128,651882665,651883047⟩]
theorem checked19890 : checkPrefixCuts (2^48) 2610954241 9 Manual.Count131072.C019890.packed 128 cuts19890 = true := by
 decide +kernel
def pointBounds19890 : List (Nat × Nat × Nat) := [(2611000320,99949618561643,99949998889531),(2611082240,99950028531773,99950408859900)]
theorem point_links_checked19890 : (cuts19890.take 2).map (fun c => (2610954241-1+2*2^9*c.k,99949391309911+c.lower,99949771637664+c.upper)) = pointBounds19890 := by
 decide +kernel
def cuts19891 : List PrefixCut := [⟨77,395727596,395727822⟩,
⟨128,657886540,657886920⟩]
theorem checked19891 : checkPrefixCuts (2^48) 2611085313 9 Manual.Count131072.C019891.packed 128 cuts19891 = true := by
 decide +kernel
def pointBounds19891 : List (Nat × Nat × Nat) := [(2611164160,99950438920172,99950819248533)]
theorem point_links_checked19891 : (cuts19891.take 1).map (fun c => (2611085313-1+2*2^9*c.k,99950043192576+c.lower,99950423520711+c.upper)) = pointBounds19891 := by
 decide +kernel
def cuts19892 : List PrefixCut := [⟨29,151881660,151881745⟩,
⟨109,554698944,554699267⟩,
⟨128,651170593,651170973⟩]
theorem checked19892 : checkPrefixCuts (2^48) 2611216385 9 Manual.Count131072.C019892.packed 128 cuts19892 = true := by
 decide +kernel
def pointBounds19892 : List (Nat × Nat × Nat) := [(2611246080,99950852960776,99951233289376),(2611328000,99951255778060,99951636106898)]
theorem point_links_checked19892 : (cuts19892.take 2).map (fun c => (2611216385-1+2*2^9*c.k,99950701079116+c.lower,99951081407631+c.upper)) = pointBounds19892 := by
 decide +kernel
def cuts19893 : List PrefixCut := [⟨61,306872022,306872200⟩,
⟨128,650383267,650383650⟩]
theorem checked19893 : checkPrefixCuts (2^48) 2611347457 9 Manual.Count131072.C019893.packed 128 cuts19893 = true := by
 decide +kernel
def pointBounds19893 : List (Nat × Nat × Nat) := [(2611409920,99951659121731,99952039450804)]
theorem point_links_checked19893 : (cuts19893.take 1).map (fun c => (2611347457-1+2*2^9*c.k,99951352249709+c.lower,99951732578604+c.upper)) = pointBounds19893 := by
 decide +kernel
def cuts19894 : List PrefixCut := [⟨13,66179046,66179086⟩,
⟨93,471114111,471114387⟩,
⟨128,648518453,648518833⟩]
theorem checked19894 : checkPrefixCuts (2^48) 2611478529 9 Manual.Count131072.C019894.packed 128 cuts19894 = true := by
 decide +kernel
def pointBounds19894 : List (Nat × Nat × Nat) := [(2611491840,99952068812022,99952449141340),(2611573760,99952473747087,99952854076641)]
theorem point_links_checked19894 : (cuts19894.take 2).map (fun c => (2611478529-1+2*2^9*c.k,99952002632976+c.lower,99952382962254+c.upper)) = pointBounds19894 := by
 decide +kernel
def cuts19895 : List PrefixCut := [⟨45,229996892,229997027⟩,
⟨125,642450845,642451222⟩,
⟨128,658293473,658293859⟩]
theorem checked19895 : checkPrefixCuts (2^48) 2611609601 9 Manual.Count131072.C019895.packed 128 cuts19895 = true := by
 decide +kernel
def pointBounds19895 : List (Nat × Nat × Nat) := [(2611655680,99952881148321,99953261478114),(2611737600,99953293602274,99953673932309)]
theorem point_links_checked19895 : (cuts19895.take 2).map (fun c => (2611609601-1+2*2^9*c.k,99952651151429+c.lower,99953031481087+c.upper)) = pointBounds19895 := by
 decide +kernel
def cuts19896 : List PrefixCut := [⟨77,388623193,388623421⟩,
⟨128,646190072,646190455⟩]
theorem checked19896 : checkPrefixCuts (2^48) 2611740673 9 Manual.Count131072.C019896.packed 128 cuts19896 = true := by
 decide +kernel
def pointBounds19896 : List (Nat × Nat × Nat) := [(2611819520,99953698068095,99954078398367)]
theorem point_links_checked19896 : (cuts19896.take 1).map (fun c => (2611740673-1+2*2^9*c.k,99953309444902+c.lower,99953689774946+c.upper)) = pointBounds19896 := by
 decide +kernel
def cuts19897 : List PrefixCut := [⟨29,148718327,148718413⟩,
⟨109,558547124,558547447⟩,
⟨128,654024689,654025067⟩]
theorem checked19897 : checkPrefixCuts (2^48) 2611871745 9 Manual.Count131072.C019897.packed 128 cuts19897 = true := by
 decide +kernel
def pointBounds19897 : List (Nat × Nat × Nat) := [(2611901440,99954104353301,99954484683814),(2611983360,99954514182098,99954894512848)]
theorem point_links_checked19897 : (cuts19897.take 2).map (fun c => (2611871745-1+2*2^9*c.k,99953955634974+c.lower,99954335965401+c.upper)) = pointBounds19897 := by
 decide +kernel
def cuts19898 : List PrefixCut := [⟨61,306795016,306795199⟩,
⟨128,642784742,642785121⟩]
theorem checked19898 : checkPrefixCuts (2^48) 2612002817 9 Manual.Count131072.C019898.packed 128 cuts19898 = true := by
 decide +kernel
def pointBounds19898 : List (Nat × Nat × Nat) := [(2612065280,99954916454679,99955296785667)]
theorem point_links_checked19898 : (cuts19898.take 1).map (fun c => (2612002817-1+2*2^9*c.k,99954609659663+c.lower,99954989990468+c.upper)) = pointBounds19898 := by
 decide +kernel
def cuts19899 : List PrefixCut := [⟨13,67024487,67024527⟩,
⟨93,471103649,471103928⟩,
⟨128,644907673,644908053⟩]
theorem checked19899 : checkPrefixCuts (2^48) 2612133889 9 Manual.Count131072.C019899.packed 128 cuts19899 = true := by
 decide +kernel
def pointBounds19899 : List (Nat × Nat × Nat) := [(2612147200,99955319468892,99955699800116),(2612229120,99955723548054,99956103879517)]
theorem point_links_checked19899 : (cuts19899.take 2).map (fun c => (2612133889-1+2*2^9*c.k,99955252444405+c.lower,99955632775589+c.upper)) = pointBounds19899 := by
 decide +kernel
def cuts19900 : List PrefixCut := [⟨45,228646195,228646326⟩,
⟨125,637979740,637980117⟩,
⟨128,652525441,652525827⟩]
theorem checked19900 : checkPrefixCuts (2^48) 2612264961 9 Manual.Count131072.C019900.packed 128 cuts19900 = true := by
 decide +kernel
def pointBounds19900 : List (Nat × Nat × Nat) := [(2612311040,99956125998273,99956506329968),(2612392960,99956535331818,99956915663759)]
theorem point_links_checked19900 : (cuts19900.take 2).map (fun c => (2612264961-1+2*2^9*c.k,99955897352078+c.lower,99956277683642+c.upper)) = pointBounds19900 := by
 decide +kernel
def cuts19901 : List PrefixCut := [⟨77,398330517,398330749⟩,
⟨128,659172810,659173192⟩]
theorem checked19901 : checkPrefixCuts (2^48) 2612396033 9 Manual.Count131072.C019901.packed 128 cuts19901 = true := by
 decide +kernel
def pointBounds19901 : List (Nat × Nat × Nat) := [(2612474880,99956948208036,99957328540218)]
theorem point_links_checked19901 : (cuts19901.take 1).map (fun c => (2612396033-1+2*2^9*c.k,99956549877519+c.lower,99956930209469+c.upper)) = pointBounds19901 := by
 decide +kernel
def cuts19902 : List PrefixCut := [⟨29,143617246,143617334⟩,
⟨109,547309853,547310175⟩,
⟨128,644379503,644379881⟩]
theorem checked19902 : checkPrefixCuts (2^48) 2612527105 9 Manual.Count131072.C019902.packed 128 cuts19902 = true := by
 decide +kernel
def pointBounds19902 : List (Nat × Nat × Nat) := [(2612556800,99957352667575,99957732999995),(2612638720,99957756360182,99958136692836)]
theorem point_links_checked19902 : (cuts19902.take 2).map (fun c => (2612527105-1+2*2^9*c.k,99957209050329+c.lower,99957589382661+c.upper)) = pointBounds19902 := by
 decide +kernel
def cuts19903 : List PrefixCut := [⟨61,310273318,310273500⟩,
⟨128,651026698,651027076⟩]
theorem checked19903 : checkPrefixCuts (2^48) 2612658177 9 Manual.Count131072.C019903.packed 128 cuts19903 = true := by
 decide +kernel
def pointBounds19903 : List (Nat × Nat × Nat) := [(2612720640,99958163703150,99958544036042)]
theorem point_links_checked19903 : (cuts19903.take 1).map (fun c => (2612658177-1+2*2^9*c.k,99957853429832+c.lower,99958233762542+c.upper)) = pointBounds19903 := by
 decide +kernel
def cuts19904 : List PrefixCut := [⟨13,63129425,63129464⟩,
⟨93,472278135,472278419⟩,
⟨128,648839398,648839786⟩]
theorem checked19904 : checkPrefixCuts (2^48) 2612789249 9 Manual.Count131072.C019904.packed 128 cuts19904 = true := by
 decide +kernel
def pointBounds19904 : List (Nat × Nat × Nat) := [(2612802560,99958567585955,99958947919082),(2612884480,99958976734665,99959357068037)]
theorem point_links_checked19904 : (cuts19904.take 2).map (fun c => (2612789249-1+2*2^9*c.k,99958504456530+c.lower,99958884789618+c.upper)) = pointBounds19904 := by
 decide +kernel
def cuts19905 : List PrefixCut := [⟨45,231820576,231820710⟩,
⟨125,639758802,639759176⟩,
⟨128,655162607,655162990⟩]
theorem checked19905 : checkPrefixCuts (2^48) 2612920321 9 Manual.Count131072.C019905.packed 128 cuts19905 = true := by
 decide +kernel
def pointBounds19905 : List (Nat × Nat × Nat) := [(2612966400,99959385116504,99959765450114),(2613048320,99959793054730,99960173388580)]
theorem point_links_checked19905 : (cuts19905.take 2).map (fun c => (2612920321-1+2*2^9*c.k,99959153295928+c.lower,99959533629404+c.upper)) = pointBounds19905 := by
 decide +kernel
def cuts19906 : List PrefixCut := [⟨77,389505469,389505698⟩,
⟨128,652759759,652760142⟩]
theorem checked19906 : checkPrefixCuts (2^48) 2613051393 9 Manual.Count131072.C019906.packed 128 cuts19906 = true := by
 decide +kernel
def pointBounds19906 : List (Nat × Nat × Nat) := [(2613130240,99960197964004,99960578298092)]
theorem point_links_checked19906 : (cuts19906.take 1).map (fun c => (2613051393-1+2*2^9*c.k,99959808458535+c.lower,99960188792394+c.upper)) = pointBounds19906 := by
 decide +kernel
def cuts19907 : List PrefixCut := [⟨29,149720837,149720924⟩,
⟨109,555035587,555035912⟩,
⟨128,655527566,655527950⟩]
theorem checked19907 : checkPrefixCuts (2^48) 2613182465 9 Manual.Count131072.C019907.packed 128 cuts19907 = true := by
 decide +kernel
def pointBounds19907 : List (Nat × Nat × Nat) := [(2613212160,99960610939131,99960991273460),(2613294080,99961016253881,99961396588448)]
theorem point_links_checked19907 : (cuts19907.take 2).map (fun c => (2613182465-1+2*2^9*c.k,99960461218294+c.lower,99960841552536+c.upper)) = pointBounds19907 := by
 decide +kernel
def cuts19908 : List PrefixCut := [⟨61,312349567,312349750⟩,
⟨128,650540310,650540688⟩]
theorem checked19908 : checkPrefixCuts (2^48) 2613313537 9 Manual.Count131072.C019908.packed 128 cuts19908 = true := by
 decide +kernel
def pointBounds19908 : List (Nat × Nat × Nat) := [(2613376000,99961429095427,99961809430236)]
theorem point_links_checked19908 : (cuts19908.take 1).map (fun c => (2613313537-1+2*2^9*c.k,99961116745860+c.lower,99961497080486+c.upper)) = pointBounds19908 := by
 decide +kernel
def cuts19909 : List PrefixCut := [⟨13,67206282,67206322⟩,
⟨93,474206059,474206341⟩,
⟨128,654277055,654277444⟩]
theorem checked19909 : checkPrefixCuts (2^48) 2613444609 9 Manual.Count131072.C019909.packed 128 cuts19909 = true := by
 decide +kernel
def pointBounds19909 : List (Nat × Nat × Nat) := [(2613457920,99961834492452,99962214827496),(2613539840,99962241492229,99962621827515)]
theorem point_links_checked19909 : (cuts19909.take 2).map (fun c => (2613444609-1+2*2^9*c.k,99961767286170+c.lower,99962147621174+c.upper)) = pointBounds19909 := by
 decide +kernel
def cuts19910 : List PrefixCut := [⟨45,228531525,228531660⟩,
⟨125,638521329,638521702⟩,
⟨128,653813579,653813962⟩]
theorem checked19910 : checkPrefixCuts (2^48) 2613575681 9 Manual.Count131072.C019910.packed 128 cuts19910 = true := by
 decide +kernel
def pointBounds19910 : List (Nat × Nat × Nat) := [(2613621760,99962650094750,99963030430278),(2613703680,99963060084554,99963440420320)]
theorem point_links_checked19910 : (cuts19910.take 2).map (fun c => (2613575681-1+2*2^9*c.k,99962421563225+c.lower,99962801898618+c.upper)) = pointBounds19910 := by
 decide +kernel
def cuts19911 : List PrefixCut := [⟨77,385853942,385854176⟩,
⟨128,649042200,649042587⟩]
theorem checked19911 : checkPrefixCuts (2^48) 2613706753 9 Manual.Count131072.C019911.packed 128 cuts19911 = true := by
 decide +kernel
def pointBounds19911 : List (Nat × Nat × Nat) := [(2613785600,99963461230746,99963841566756)]
theorem point_links_checked19911 : (cuts19911.take 1).map (fun c => (2613706753-1+2*2^9*c.k,99963075376804+c.lower,99963455712580+c.upper)) = pointBounds19911 := by
 decide +kernel
def cuts19912 : List PrefixCut := [⟨29,147529586,147529674⟩,
⟨109,555650170,555650502⟩,
⟨128,656440012,656440402⟩]
theorem checked19912 : checkPrefixCuts (2^48) 2613837825 9 Manual.Count131072.C019912.packed 128 cuts19912 = true := by
 decide +kernel
def pointBounds19912 : List (Nat × Nat × Nat) := [(2613867520,99963871948590,99964252284841),(2613949440,99964280069174,99964660405669)]
theorem point_links_checked19912 : (cuts19912.take 2).map (fun c => (2613837825-1+2*2^9*c.k,99963724419004+c.lower,99964104755167+c.upper)) = pointBounds19912 := by
 decide +kernel
def cuts19913 : List PrefixCut := [⟨61,318086030,318086213⟩,
⟨128,653930702,653931088⟩]
theorem checked19913 : checkPrefixCuts (2^48) 2613968897 9 Manual.Count131072.C019913.packed 128 cuts19913 = true := by
 decide +kernel
def pointBounds19913 : List (Nat × Nat × Nat) := [(2614031360,99964698945046,99965079281782)]
theorem point_links_checked19913 : (cuts19913.take 1).map (fun c => (2613968897-1+2*2^9*c.k,99964380859016+c.lower,99964761195569+c.upper)) = pointBounds19913 := by
 decide +kernel
def cuts19914 : List PrefixCut := [⟨13,65358949,65358987⟩,
⟨93,467949782,467950061⟩,
⟨128,643668825,643669209⟩]
theorem checked19914 : checkPrefixCuts (2^48) 2614099969 9 Manual.Count131072.C019914.packed 128 cuts19914 = true := by
 decide +kernel
def pointBounds19914 : List (Nat × Nat × Nat) := [(2614113280,99965100148667,99965480485644),(2614195200,99965502739500,99965883076718)]
theorem point_links_checked19914 : (cuts19914.take 2).map (fun c => (2614099969-1+2*2^9*c.k,99965034789718+c.lower,99965415126657+c.upper)) = pointBounds19914 := by
 decide +kernel
def cuts19915 : List PrefixCut := [⟨45,225244157,225244292⟩,
⟨125,630824456,630824830⟩,
⟨128,646651198,646651582⟩]
theorem checked19915 : checkPrefixCuts (2^48) 2614231041 9 Manual.Count131072.C019915.packed 128 cuts19915 = true := by
 decide +kernel
def pointBounds19915 : List (Nat × Nat × Nat) := [(2614277120,99965903702700,99966284040158),(2614359040,99966309282999,99966689620696)]
theorem point_links_checked19915 : (cuts19915.take 2).map (fun c => (2614231041-1+2*2^9*c.k,99965678458543+c.lower,99966058795866+c.upper)) = pointBounds19915 := by
 decide +kernel
def cuts19916 : List PrefixCut := [⟨77,395662416,395662647⟩,
⟨128,657385141,657385526⟩]
theorem checked19916 : checkPrefixCuts (2^48) 2614362113 9 Manual.Count131072.C019916.packed 128 cuts19916 = true := by
 decide +kernel
def pointBounds19916 : List (Nat × Nat × Nat) := [(2614440960,99966720772157,99967101110095)]
theorem point_links_checked19916 : (cuts19916.take 1).map (fun c => (2614362113-1+2*2^9*c.k,99966325109741+c.lower,99966705447448+c.upper)) = pointBounds19916 := by
 decide +kernel
def cuts19917 : List PrefixCut := [⟨29,143293903,143293985⟩,
⟨109,544529822,544530142⟩,
⟨128,645725007,645725383⟩]
theorem checked19917 : checkPrefixCuts (2^48) 2614493185 9 Manual.Count131072.C019917.packed 128 cuts19917 = true := by
 decide +kernel
def pointBounds19917 : List (Nat × Nat × Nat) := [(2614522880,99967125788785,99967506126959),(2614604800,99967527024704,99967907363116)]
theorem point_links_checked19917 : (cuts19917.take 2).map (fun c => (2614493185-1+2*2^9*c.k,99966982494882+c.lower,99967362832974+c.upper)) = pointBounds19917 := by
 decide +kernel
def cuts19918 : List PrefixCut := [⟨61,301966052,301966230⟩,
⟨128,632882357,632882726⟩]
theorem checked19918 : checkPrefixCuts (2^48) 2614624257 9 Manual.Count131072.C019918.packed 128 cuts19918 = true := by
 decide +kernel
def pointBounds19918 : List (Nat × Nat × Nat) := [(2614686720,99967930185941,99968310524587)]
theorem point_links_checked19918 : (cuts19918.take 1).map (fun c => (2614624257-1+2*2^9*c.k,99967628219889+c.lower,99968008558357+c.upper)) = pointBounds19918 := by
 decide +kernel
def cuts19919 : List PrefixCut := [⟨13,66419057,66419098⟩,
⟨93,480965441,480965725⟩,
⟨128,656532793,656533181⟩]
theorem checked19919 : checkPrefixCuts (2^48) 2614755329 9 Manual.Count131072.C019919.packed 128 cuts19919 = true := by
 decide +kernel
def pointBounds19919 : List (Nat × Nat × Nat) := [(2614768640,99968327521303,99968707860181),(2614850560,99968742067687,99969122406808)]
theorem point_links_checked19919 : (cuts19919.take 2).map (fun c => (2614755329-1+2*2^9*c.k,99968261102246+c.lower,99968641441083+c.upper)) = pointBounds19919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000309
