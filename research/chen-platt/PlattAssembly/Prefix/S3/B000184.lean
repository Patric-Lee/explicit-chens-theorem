import PlattAssemblyKernel
import PlattCertificates.Count131072.C025888
import PlattCertificates.Count131072.C025889
import PlattCertificates.Count131072.C025890
import PlattCertificates.Count131072.C025891
import PlattCertificates.Count131072.C025892
import PlattCertificates.Count131072.C025893
import PlattCertificates.Count131072.C025894
import PlattCertificates.Count131072.C025895
import PlattCertificates.Count131072.C025896
import PlattCertificates.Count131072.C025897
import PlattCertificates.Count131072.C025898
import PlattCertificates.Count131072.C025899
import PlattCertificates.Count131072.C025900
import PlattCertificates.Count131072.C025901
import PlattCertificates.Count131072.C025902
import PlattCertificates.Count131072.C025903
import PlattCertificates.Count131072.C025904
import PlattCertificates.Count131072.C025905
import PlattCertificates.Count131072.C025906
import PlattCertificates.Count131072.C025907
import PlattCertificates.Count131072.C025908
import PlattCertificates.Count131072.C025909
import PlattCertificates.Count131072.C025910
import PlattCertificates.Count131072.C025911
import PlattCertificates.Count131072.C025912
import PlattCertificates.Count131072.C025913
import PlattCertificates.Count131072.C025914
import PlattCertificates.Count131072.C025915
import PlattCertificates.Count131072.C025916
import PlattCertificates.Count131072.C025917
import PlattCertificates.Count131072.C025918
import PlattCertificates.Count131072.C025919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25888 : List PrefixCut := [⟨62,240613931,240614064⟩,
⟨128,497131308,497131585⟩]
theorem checked25888 : checkPrefixCuts (2^48) 3397124097 9 Manual.Count131072.C025888.packed 128 cuts25888 = true := by
 decide +kernel
def pointBounds25888 : List (Nat × Nat × Nat) := [(3397187584,103345711483910,103346093751247)]
theorem point_links_checked25888 : (cuts25888.take 1).map (fun c => (3397124097-1+2*2^9*c.k,103345470869979+c.lower,103345853137183+c.upper)) = pointBounds25888 := by
 decide +kernel
def cuts25889 : List PrefixCut := [⟨38,145407273,145407355⟩,
⟨128,494875089,494875366⟩]
theorem checked25889 : checkPrefixCuts (2^48) 3397255169 9 Manual.Count131072.C025889.packed 128 cuts25889 = true := by
 decide +kernel
def pointBounds25889 : List (Nat × Nat × Nat) := [(3397294080,103346113408560,103346495676123)]
theorem point_links_checked25889 : (cuts25889.take 1).map (fun c => (3397255169-1+2*2^9*c.k,103345968001287+c.lower,103346350268768+c.upper)) = pointBounds25889 := by
 decide +kernel
def cuts25890 : List PrefixCut := [⟨14,56006771,56006803⟩,
⟨118,455337944,455338197⟩,
⟨128,492619253,492619528⟩]
theorem checked25890 : checkPrefixCuts (2^48) 3397386241 9 Manual.Count131072.C025890.packed 128 cuts25890 = true := by
 decide +kernel
def pointBounds25890 : List (Nat × Nat × Nat) := [(3397400576,103346518883147,103346901150937),(3397507072,103346918214320,103347300482331)]
theorem point_links_checked25890 : (cuts25890.take 2).map (fun c => (3397386241-1+2*2^9*c.k,103346462876376+c.lower,103346845144134+c.upper)) = pointBounds25890 := by
 decide +kernel
def cuts25891 : List PrefixCut := [⟨94,362865719,362865922⟩,
⟨128,496410978,496411257⟩]
theorem checked25891 : checkPrefixCuts (2^48) 3397517313 9 Manual.Count131072.C025891.packed 128 cuts25891 = true := by
 decide +kernel
def pointBounds25891 : List (Nat × Nat × Nat) := [(3397613568,103347318361348,103347700629584)]
theorem point_links_checked25891 : (cuts25891.take 1).map (fun c => (3397517313-1+2*2^9*c.k,103346955495629+c.lower,103347337763662+c.upper)) = pointBounds25891 := by
 decide +kernel
def cuts25892 : List PrefixCut := [⟨70,272636838,272636989⟩,
⟨128,495894850,495895123⟩]
theorem checked25892 : checkPrefixCuts (2^48) 3397648385 9 Manual.Count131072.C025892.packed 128 cuts25892 = true := by
 decide +kernel
def pointBounds25892 : List (Nat × Nat × Nat) := [(3397720064,103347724543445,103348106811908)]
theorem point_links_checked25892 : (cuts25892.take 1).map (fun c => (3397648385-1+2*2^9*c.k,103347451906607+c.lower,103347834174919+c.upper)) = pointBounds25892 := by
 decide +kernel
def cuts25893 : List PrefixCut := [⟨46,172887639,172887737⟩,
⟨128,482372970,482373240⟩]
theorem checked25893 : checkPrefixCuts (2^48) 3397779457 9 Manual.Count131072.C025893.packed 128 cuts25893 = true := by
 decide +kernel
def pointBounds25893 : List (Nat × Nat × Nat) := [(3397826560,103348120689096,103348502957779)]
theorem point_links_checked25893 : (cuts25893.take 1).map (fun c => (3397779457-1+2*2^9*c.k,103347947801457+c.lower,103348330070042+c.upper)) = pointBounds25893 := by
 decide +kernel
def cuts25894 : List PrefixCut := [⟨22,82506021,82506069⟩,
⟨126,483679832,483680098⟩,
⟨128,489975252,489975522⟩]
theorem checked25894 : checkPrefixCuts (2^48) 3397910529 9 Manual.Count131072.C025894.packed 128 cuts25894 = true := by
 decide +kernel
def pointBounds25894 : List (Nat × Nat × Nat) := [(3397933056,103348512680448,103348894949351),(3398039552,103348913854259,103349296123380)]
theorem point_links_checked25894 : (cuts25894.take 2).map (fun c => (3397910529-1+2*2^9*c.k,103348430174427+c.lower,103348812443282+c.upper)) = pointBounds25894 := by
 decide +kernel
def cuts25895 : List PrefixCut := [⟨102,398427578,398427796⟩,
⟨128,499067947,499068222⟩]
theorem checked25895 : checkPrefixCuts (2^48) 3398041601 9 Manual.Count131072.C025895.packed 128 cuts25895 = true := by
 decide +kernel
def pointBounds25895 : List (Nat × Nat × Nat) := [(3398146048,103349318577257,103349700846600)]
theorem point_links_checked25895 : (cuts25895.take 1).map (fun c => (3398041601-1+2*2^9*c.k,103348920149679+c.lower,103349302418804+c.upper)) = pointBounds25895 := by
 decide +kernel
def cuts25896 : List PrefixCut := [⟨78,302082056,302082223⟩,
⟨128,492505180,492505458⟩]
theorem checked25896 : checkPrefixCuts (2^48) 3398172673 9 Manual.Count131072.C025896.packed 128 cuts25896 = true := by
 decide +kernel
def pointBounds25896 : List (Nat × Nat × Nat) := [(3398252544,103349721299682,103350103569249)]
theorem point_links_checked25896 : (cuts25896.take 1).map (fun c => (3398172673-1+2*2^9*c.k,103349419217626+c.lower,103349801487026+c.upper)) = pointBounds25896 := by
 decide +kernel
def cuts25897 : List PrefixCut := [⟨54,209056307,209056422⟩,
⟨128,498035473,498035754⟩]
theorem checked25897 : checkPrefixCuts (2^48) 3398303745 9 Manual.Count131072.C025897.packed 128 cuts25897 = true := by
 decide +kernel
def pointBounds25897 : List (Nat × Nat × Nat) := [(3398359040,103350120779113,103350503048906)]
theorem point_links_checked25897 : (cuts25897.take 1).map (fun c => (3398303745-1+2*2^9*c.k,103349911722806+c.lower,103350293992484+c.upper)) = pointBounds25897 := by
 decide +kernel
def cuts25898 : List PrefixCut := [⟨30,113966490,113966554⟩,
⟨128,490644997,490645272⟩]
theorem checked25898 : checkPrefixCuts (2^48) 3398434817 9 Manual.Count131072.C025898.packed 128 cuts25898 = true := by
 decide +kernel
def pointBounds25898 : List (Nat × Nat × Nat) := [(3398465536,103350523724769,103350905994792)]
theorem point_links_checked25898 : (cuts25898.take 1).map (fun c => (3398434817-1+2*2^9*c.k,103350409758279+c.lower,103350792028238+c.upper)) = pointBounds25898 := by
 decide +kernel
def cuts25899 : List PrefixCut := [⟨6,21285149,21285162⟩,
⟨110,423625778,423626018⟩,
⟨128,494270126,494270405⟩]
theorem checked25899 : checkPrefixCuts (2^48) 3398565889 9 Manual.Count131072.C025899.packed 128 cuts25899 = true := by
 decide +kernel
def pointBounds25899 : List (Nat × Nat × Nat) := [(3398572032,103350921688425,103351303958672),(3398678528,103351324029054,103351706299528)]
theorem point_links_checked25899 : (cuts25899.take 2).map (fun c => (3398565889-1+2*2^9*c.k,103350900403276+c.lower,103351282673510+c.upper)) = pointBounds25899 := by
 decide +kernel
def cuts25900 : List PrefixCut := [⟨86,333340010,333340194⟩,
⟨128,496569966,496570243⟩]
theorem checked25900 : checkPrefixCuts (2^48) 3398696961 9 Manual.Count131072.C025900.packed 128 cuts25900 = true := by
 decide +kernel
def pointBounds25900 : List (Nat × Nat × Nat) := [(3398785024,103351728013412,103352110284109)]
theorem point_links_checked25900 : (cuts25900.take 1).map (fun c => (3398696961-1+2*2^9*c.k,103351394673402+c.lower,103351776943915+c.upper)) = pointBounds25900 := by
 decide +kernel
def cuts25901 : List PrefixCut := [⟨62,240824573,240824711⟩,
⟨128,493735196,493735477⟩]
theorem checked25901 : checkPrefixCuts (2^48) 3398828033 9 Manual.Count131072.C025901.packed 128 cuts25901 = true := by
 decide +kernel
def pointBounds25901 : List (Nat × Nat × Nat) := [(3398891520,103352132067941,103352514338869)]
theorem point_links_checked25901 : (cuts25901.take 1).map (fun c => (3398828033-1+2*2^9*c.k,103351891243368+c.lower,103352273514158+c.upper)) = pointBounds25901 := by
 decide +kernel
def cuts25902 : List PrefixCut := [⟨38,150220259,150220343⟩,
⟨128,499512950,499513235⟩]
theorem checked25902 : checkPrefixCuts (2^48) 3398959105 9 Manual.Count131072.C025902.packed 128 cuts25902 = true := by
 decide +kernel
def pointBounds25902 : List (Nat × Nat × Nat) := [(3398998016,103352535198823,103352917469978)]
theorem point_links_checked25902 : (cuts25902.take 1).map (fun c => (3398959105-1+2*2^9*c.k,103352384978564+c.lower,103352767249635+c.upper)) = pointBounds25902 := by
 decide +kernel
def cuts25903 : List PrefixCut := [⟨14,53080389,53080420⟩,
⟨118,457593739,457593995⟩,
⟨128,497174926,497175203⟩]
theorem checked25903 : checkPrefixCuts (2^48) 3399090177 9 Manual.Count131072.C025903.packed 128 cuts25903 = true := by
 decide +kernel
def pointBounds25903 : List (Nat × Nat × Nat) := [(3399104512,103352937571903,103353319843290),(3399211008,103353342085253,103353724356865)]
theorem point_links_checked25903 : (cuts25903.take 2).map (fun c => (3399090177-1+2*2^9*c.k,103352884491514+c.lower,103353266762870+c.upper)) = pointBounds25903 := by
 decide +kernel
def cuts25904 : List PrefixCut := [⟨94,360199733,360199939⟩,
⟨128,494340482,494340762⟩]
theorem checked25904 : checkPrefixCuts (2^48) 3399221249 9 Manual.Count131072.C025904.packed 128 cuts25904 = true := by
 decide +kernel
def pointBounds25904 : List (Nat × Nat × Nat) := [(3399317504,103353741866173,103354124138012)]
theorem point_links_checked25904 : (cuts25904.take 1).map (fun c => (3399221249-1+2*2^9*c.k,103353381666440+c.lower,103353763938073+c.upper)) = pointBounds25904 := by
 decide +kernel
def cuts25905 : List PrefixCut := [⟨70,271506560,271506709⟩,
⟨128,495149433,495149709⟩]
theorem checked25905 : checkPrefixCuts (2^48) 3399352321 9 Manual.Count131072.C025905.packed 128 cuts25905 = true := by
 decide +kernel
def pointBounds25905 : List (Nat × Nat × Nat) := [(3399424000,103354147513482,103354529785544)]
theorem point_links_checked25905 : (cuts25905.take 1).map (fun c => (3399352321-1+2*2^9*c.k,103353876006922+c.lower,103354258278835+c.upper)) = pointBounds25905 := by
 decide +kernel
def cuts25906 : List PrefixCut := [⟨46,178017321,178017419⟩,
⟨128,496786348,496786626⟩]
theorem checked25906 : checkPrefixCuts (2^48) 3399483393 9 Manual.Count131072.C025906.packed 128 cuts25906 = true := by
 decide +kernel
def pointBounds25906 : List (Nat × Nat × Nat) := [(3399530496,103354549173676,103354931445963)]
theorem point_links_checked25906 : (cuts25906.take 1).map (fun c => (3399483393-1+2*2^9*c.k,103354371156355+c.lower,103354753428544+c.upper)) = pointBounds25906 := by
 decide +kernel
def cuts25907 : List PrefixCut := [⟨22,86521654,86521700⟩,
⟨126,483685783,483686051⟩,
⟨128,491633907,491634179⟩]
theorem checked25907 : checkPrefixCuts (2^48) 3399614465 9 Manual.Count131072.C025907.packed 128 cuts25907 = true := by
 decide +kernel
def pointBounds25907 : List (Nat × Nat × Nat) := [(3399636992,103354954464357,103355336736870),(3399743488,103355351628486,103355733901221)]
theorem point_links_checked25907 : (cuts25907.take 2).map (fun c => (3399614465-1+2*2^9*c.k,103354867942703+c.lower,103355250215170+c.upper)) = pointBounds25907 := by
 decide +kernel
def cuts25908 : List PrefixCut := [⟨102,392763636,392763860⟩,
⟨128,491201020,491201305⟩]
theorem checked25908 : checkPrefixCuts (2^48) 3399745537 9 Manual.Count131072.C025908.packed 128 cuts25908 = true := by
 decide +kernel
def pointBounds25908 : List (Nat × Nat × Nat) := [(3399849984,103355752340246,103356134613209)]
theorem point_links_checked25908 : (cuts25908.take 1).map (fun c => (3399745537-1+2*2^9*c.k,103355359576610+c.lower,103355741849349+c.upper)) = pointBounds25908 := by
 decide +kernel
def cuts25909 : List PrefixCut := [⟨78,302675738,302675910⟩,
⟨128,493417384,493417660⟩]
theorem checked25909 : checkPrefixCuts (2^48) 3399876609 9 Manual.Count131072.C025909.packed 128 cuts25909 = true := by
 decide +kernel
def pointBounds25909 : List (Nat × Nat × Nat) := [(3399956480,103356153453368,103356535726564)]
theorem point_links_checked25909 : (cuts25909.take 1).map (fun c => (3399876609-1+2*2^9*c.k,103355850777630+c.lower,103356233050654+c.upper)) = pointBounds25909 := by
 decide +kernel
def cuts25910 : List PrefixCut := [⟨54,206716307,206716423⟩,
⟨128,499772683,499772958⟩]
theorem checked25910 : checkPrefixCuts (2^48) 3400007681 9 Manual.Count131072.C025910.packed 128 cuts25910 = true := by
 decide +kernel
def pointBounds25910 : List (Nat × Nat × Nat) := [(3400062976,103356550911321,103356933184737)]
theorem point_links_checked25910 : (cuts25910.take 1).map (fun c => (3400007681-1+2*2^9*c.k,103356344195014+c.lower,103356726468314+c.upper)) = pointBounds25910 := by
 decide +kernel
def cuts25911 : List PrefixCut := [⟨30,117055158,117055222⟩,
⟨128,496442249,496442527⟩]
theorem checked25911 : checkPrefixCuts (2^48) 3400138753 9 Manual.Count131072.C025911.packed 128 cuts25911 = true := by
 decide +kernel
def pointBounds25911 : List (Nat × Nat × Nat) := [(3400169472,103356961022855,103357343296494)]
theorem point_links_checked25911 : (cuts25911.take 1).map (fun c => (3400138753-1+2*2^9*c.k,103356843967697+c.lower,103357226241272+c.upper)) = pointBounds25911 := by
 decide +kernel
def cuts25912 : List PrefixCut := [⟨6,23178425,23178439⟩,
⟨110,428380258,428380504⟩,
⟨128,495926447,495926731⟩]
theorem checked25912 : checkPrefixCuts (2^48) 3400269825 9 Manual.Count131072.C025912.packed 128 cuts25912 = true := by
 decide +kernel
def pointBounds25912 : List (Nat × Nat × Nat) := [(3400275968,103357363588371,103357745862238),(3400382464,103357768790204,103358151064303)]
theorem point_links_checked25912 : (cuts25912.take 2).map (fun c => (3400269825-1+2*2^9*c.k,103357340409946+c.lower,103357722683799+c.upper)) = pointBounds25912 := by
 decide +kernel
def cuts25913 : List PrefixCut := [⟨86,333172996,333173178⟩,
⟨128,496652249,496652522⟩]
theorem checked25913 : checkPrefixCuts (2^48) 3400400897 9 Manual.Count131072.C025913.packed 128 cuts25913 = true := by
 decide +kernel
def pointBounds25913 : List (Nat × Nat × Nat) := [(3400488960,103358169509389,103358551783708)]
theorem point_links_checked25913 : (cuts25913.take 1).map (fun c => (3400400897-1+2*2^9*c.k,103357836336393+c.lower,103358218610530+c.upper)) = pointBounds25913 := by
 decide +kernel
def cuts25914 : List PrefixCut := [⟨62,242938792,242938922⟩,
⟨128,500275161,500275432⟩]
theorem checked25914 : checkPrefixCuts (2^48) 3400531969 9 Manual.Count131072.C025914.packed 128 cuts25914 = true := by
 decide +kernel
def pointBounds25914 : List (Nat × Nat × Nat) := [(3400595456,103358575927434,103358958201974)]
theorem point_links_checked25914 : (cuts25914.take 1).map (fun c => (3400531969-1+2*2^9*c.k,103358332988642+c.lower,103358715263052+c.upper)) = pointBounds25914 := by
 decide +kernel
def cuts25915 : List PrefixCut := [⟨38,146337555,146337638⟩,
⟨128,490240798,490241074⟩]
theorem checked25915 : checkPrefixCuts (2^48) 3400663041 9 Manual.Count131072.C025915.packed 128 cuts25915 = true := by
 decide +kernel
def pointBounds25915 : List (Nat × Nat × Nat) := [(3400701952,103358979601358,103359361876122)]
theorem point_links_checked25915 : (cuts25915.take 1).map (fun c => (3400663041-1+2*2^9*c.k,103358833263803+c.lower,103359215538484+c.upper)) = pointBounds25915 := by
 decide +kernel
def cuts25916 : List PrefixCut := [⟨14,56198949,56198980⟩,
⟨118,455791990,455792242⟩,
⟨128,493780822,493781095⟩]
theorem checked25916 : checkPrefixCuts (2^48) 3400794113 9 Manual.Count131072.C025916.packed 128 cuts25916 = true := by
 decide +kernel
def pointBounds25916 : List (Nat × Nat × Nat) := [(3400808448,103359379703550,103359761978538),(3400914944,103359779296591,103360161571800)]
theorem point_links_checked25916 : (cuts25916.take 2).map (fun c => (3400794113-1+2*2^9*c.k,103359323504601+c.lower,103359705779558+c.upper)) = pointBounds25916 := by
 decide +kernel
def cuts25917 : List PrefixCut := [⟨94,360846891,360847091⟩,
⟨128,492106548,492106824⟩]
theorem checked25917 : checkPrefixCuts (2^48) 3400925185 9 Manual.Count131072.C025917.packed 128 cuts25917 = true := by
 decide +kernel
def pointBounds25917 : List (Nat × Nat × Nat) := [(3401021440,103360178132314,103360560407744)]
theorem point_links_checked25917 : (cuts25917.take 1).map (fun c => (3400925185-1+2*2^9*c.k,103359817285423+c.lower,103360199560653+c.upper)) = pointBounds25917 := by
 decide +kernel
def cuts25918 : List PrefixCut := [⟨70,269880859,269881004⟩,
⟨128,492666886,492667158⟩]
theorem checked25918 : checkPrefixCuts (2^48) 3401056257 9 Manual.Count131072.C025918.packed 128 cuts25918 = true := by
 decide +kernel
def pointBounds25918 : List (Nat × Nat × Nat) := [(3401127936,103360579272830,103360961548481)]
theorem point_links_checked25918 : (cuts25918.take 1).map (fun c => (3401056257-1+2*2^9*c.k,103360309391971+c.lower,103360691667477+c.upper)) = pointBounds25918 := by
 decide +kernel
def cuts25919 : List PrefixCut := [⟨46,179252235,179252339⟩,
⟨128,497530532,497530815⟩]
theorem checked25919 : checkPrefixCuts (2^48) 3401187329 9 Manual.Count131072.C025919.packed 128 cuts25919 = true := by
 decide +kernel
def pointBounds25919 : List (Nat × Nat × Nat) := [(3401234432,103360981311092,103361363586974)]
theorem point_links_checked25919 : (cuts25919.take 1).map (fun c => (3401187329-1+2*2^9*c.k,103360802058857+c.lower,103361184334635+c.upper)) = pointBounds25919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000184
