import PlattAssemblyKernel
import PlattCertificates.Count131072.C030000
import PlattCertificates.Count131072.C030001
import PlattCertificates.Count131072.C030002
import PlattCertificates.Count131072.C030003
import PlattCertificates.Count131072.C030004
import PlattCertificates.Count131072.C030005
import PlattCertificates.Count131072.C030006
import PlattCertificates.Count131072.C030007
import PlattCertificates.Count131072.C030008
import PlattCertificates.Count131072.C030009
import PlattCertificates.Count131072.C030010
import PlattCertificates.Count131072.C030011
import PlattCertificates.Count131072.C030012
import PlattCertificates.Count131072.C030013
import PlattCertificates.Count131072.C030014
import PlattCertificates.Count131072.C030015
import PlattCertificates.Count131072.C030016
import PlattCertificates.Count131072.C030017
import PlattCertificates.Count131072.C030018
import PlattCertificates.Count131072.C030019
import PlattCertificates.Count131072.C030020
import PlattCertificates.Count131072.C030021
import PlattCertificates.Count131072.C030022
import PlattCertificates.Count131072.C030023
import PlattCertificates.Count131072.C030024
import PlattCertificates.Count131072.C030025
import PlattCertificates.Count131072.C030026
import PlattCertificates.Count131072.C030027
import PlattCertificates.Count131072.C030028
import PlattCertificates.Count131072.C030029
import PlattCertificates.Count131072.C030030
import PlattCertificates.Count131072.C030031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30000 : List PrefixCut := [⟨4,13301086,13301093⟩,
⟨125,411683595,411683821⟩,
⟨128,422195404,422195635⟩]
theorem checked30000 : checkPrefixCuts (2^48) 3936092161 9 Manual.Count131072.C030000.packed 128 cuts30000 = true := by
 decide +kernel
def pointBounds30000 : List (Nat × Nat × Nat) := [(3936096256,105227972908960,105228356230290),(3936220160,105228371291469,105228754613018)]
theorem point_links_checked30000 : (cuts30000.take 2).map (fun c => (3936092161-1+2*2^9*c.k,105227959607874+c.lower,105228342929197+c.upper)) = pointBounds30000 := by
 decide +kernel
def cuts30001 : List PrefixCut := [⟨118,388930805,388931025⟩,
⟨128,423039449,423039687⟩]
theorem checked30001 : checkPrefixCuts (2^48) 3936223233 9 Manual.Count131072.C030001.packed 128 cuts30001 = true := by
 decide +kernel
def pointBounds30001 : List (Nat × Nat × Nat) := [(3936344064,105228770734083,105229154055857)]
theorem point_links_checked30001 : (cuts30001.take 1).map (fun c => (3936223233-1+2*2^9*c.k,105228381803278+c.lower,105228765124832+c.upper)) = pointBounds30001 := by
 decide +kernel
def cuts30002 : List PrefixCut := [⟨111,372185882,372186090⟩,
⟨128,428960270,428960511⟩]
theorem checked30002 : checkPrefixCuts (2^48) 3936354305 9 Manual.Count131072.C030002.packed 128 cuts30002 = true := by
 decide +kernel
def pointBounds30002 : List (Nat × Nat × Nat) := [(3936467968,105229177028609,105229560350609)]
theorem point_links_checked30002 : (cuts30002.take 1).map (fun c => (3936354305-1+2*2^9*c.k,105228804842727+c.lower,105229188164519+c.upper)) = pointBounds30002 := by
 decide +kernel
def cuts30003 : List PrefixCut := [⟨104,345002676,345002868⟩,
⟨128,425728386,425728623⟩]
theorem checked30003 : checkPrefixCuts (2^48) 3936485377 9 Manual.Count131072.C030003.packed 128 cuts30003 = true := by
 decide +kernel
def pointBounds30003 : List (Nat × Nat × Nat) := [(3936591872,105229578805673,105229962127898)]
theorem point_links_checked30003 : (cuts30003.take 1).map (fun c => (3936485377-1+2*2^9*c.k,105229233802997+c.lower,105229617125030+c.upper)) = pointBounds30003 := by
 decide +kernel
def cuts30004 : List PrefixCut := [⟨97,321253209,321253388⟩,
⟨128,423926694,423926933⟩]
theorem checked30004 : checkPrefixCuts (2^48) 3936616449 9 Manual.Count131072.C030004.packed 128 cuts30004 = true := by
 decide +kernel
def pointBounds30004 : List (Nat × Nat × Nat) := [(3936715776,105229980784592,105230364107041)]
theorem point_links_checked30004 : (cuts30004.take 1).map (fun c => (3936616449-1+2*2^9*c.k,105229659531383+c.lower,105230042853653+c.upper)) = pointBounds30004 := by
 decide +kernel
def cuts30005 : List PrefixCut := [⟨90,299435755,299435919⟩,
⟨128,423769607,423769839⟩]
theorem checked30005 : checkPrefixCuts (2^48) 3936747521 9 Manual.Count131072.C030005.packed 128 cuts30005 = true := by
 decide +kernel
def pointBounds30005 : List (Nat × Nat × Nat) := [(3936839680,105230382893832,105230766216505)]
theorem point_links_checked30005 : (cuts30005.take 1).map (fun c => (3936747521-1+2*2^9*c.k,105230083458077+c.lower,105230466780586+c.upper)) = pointBounds30005 := by
 decide +kernel
def cuts30006 : List PrefixCut := [⟨83,271113584,271113733⟩,
⟨128,424827842,424828077⟩]
theorem checked30006 : checkPrefixCuts (2^48) 3936878593 9 Manual.Count131072.C030006.packed 128 cuts30006 = true := by
 decide +kernel
def pointBounds30006 : List (Nat × Nat × Nat) := [(3936963584,105230778341268,105231161664158)]
theorem point_links_checked30006 : (cuts30006.take 1).map (fun c => (3936878593-1+2*2^9*c.k,105230507227684+c.lower,105230890550425+c.upper)) = pointBounds30006 := by
 decide +kernel
def cuts30007 : List PrefixCut := [⟨76,248298248,248298391⟩,
⟨128,422954898,422955136⟩]
theorem checked30007 : checkPrefixCuts (2^48) 3937009665 9 Manual.Count131072.C030007.packed 128 cuts30007 = true := by
 decide +kernel
def pointBounds30007 : List (Nat × Nat × Nat) := [(3937087488,105231180353774,105231563676893)]
theorem point_links_checked30007 : (cuts30007.take 1).map (fun c => (3937009665-1+2*2^9*c.k,105230932055526+c.lower,105231315378502+c.upper)) = pointBounds30007 := by
 decide +kernel
def cuts30008 : List PrefixCut := [⟨69,229201966,229202091⟩,
⟨128,423870274,423870509⟩]
theorem checked30008 : checkPrefixCuts (2^48) 3937140737 9 Manual.Count131072.C030008.packed 128 cuts30008 = true := by
 decide +kernel
def pointBounds30008 : List (Nat × Nat × Nat) := [(3937211392,105231584212390,105231967535729)]
theorem point_links_checked30008 : (cuts30008.take 1).map (fun c => (3937140737-1+2*2^9*c.k,105231355010424+c.lower,105231738333638+c.upper)) = pointBounds30008 := by
 decide +kernel
def cuts30009 : List PrefixCut := [⟨62,203815873,203815987⟩,
⟨128,426858653,426858893⟩]
theorem checked30009 : checkPrefixCuts (2^48) 3937271809 9 Manual.Count131072.C030009.packed 128 cuts30009 = true := by
 decide +kernel
def pointBounds30009 : List (Nat × Nat × Nat) := [(3937335296,105231982696571,105232366020134)]
theorem point_links_checked30009 : (cuts30009.take 1).map (fun c => (3937271809-1+2*2^9*c.k,105231778880698+c.lower,105232162204147+c.upper)) = pointBounds30009 := by
 decide +kernel
def cuts30010 : List PrefixCut := [⟨55,183006573,183006676⟩,
⟨128,424413958,424414196⟩]
theorem checked30010 : checkPrefixCuts (2^48) 3937402881 9 Manual.Count131072.C030010.packed 128 cuts30010 = true := by
 decide +kernel
def pointBounds30010 : List (Nat × Nat × Nat) := [(3937459200,105232388745924,105232772069716)]
theorem point_links_checked30010 : (cuts30010.take 1).map (fun c => (3937402881-1+2*2^9*c.k,105232205739351+c.lower,105232589063040+c.upper)) = pointBounds30010 := by
 decide +kernel
def cuts30011 : List PrefixCut := [⟨48,157695082,157695174⟩,
⟨128,427902447,427902687⟩]
theorem checked30011 : checkPrefixCuts (2^48) 3937533953 9 Manual.Count131072.C030011.packed 128 cuts30011 = true := by
 decide +kernel
def pointBounds30011 : List (Nat × Nat × Nat) := [(3937583104,105232787848391,105233171172410)]
theorem point_links_checked30011 : (cuts30011.take 1).map (fun c => (3937533953-1+2*2^9*c.k,105232630153309+c.lower,105233013477236+c.upper)) = pointBounds30011 := by
 decide +kernel
def cuts30012 : List PrefixCut := [⟨41,136817146,136817222⟩,
⟨128,423027529,423027761⟩]
theorem checked30012 : checkPrefixCuts (2^48) 3937665025 9 Manual.Count131072.C030012.packed 128 cuts30012 = true := by
 decide +kernel
def pointBounds30012 : List (Nat × Nat × Nat) := [(3937707008,105233194872902,105233578197145)]
theorem point_links_checked30012 : (cuts30012.take 1).map (fun c => (3937665025-1+2*2^9*c.k,105233058055756+c.lower,105233441379923+c.upper)) = pointBounds30012 := by
 decide +kernel
def cuts30013 : List PrefixCut := [⟨34,113867630,113867691⟩,
⟨128,427159248,427159481⟩]
theorem checked30013 : checkPrefixCuts (2^48) 3937796097 9 Manual.Count131072.C030013.packed 128 cuts30013 = true := by
 decide +kernel
def pointBounds30013 : List (Nat × Nat × Nat) := [(3937830912,105233594950915,105233978275375)]
theorem point_links_checked30013 : (cuts30013.take 1).map (fun c => (3937796097-1+2*2^9*c.k,105233481083285+c.lower,105233864407684+c.upper)) = pointBounds30013 := by
 decide +kernel
def cuts30014 : List PrefixCut := [⟨27,90705178,90705229⟩,
⟨128,428074232,428074466⟩]
theorem checked30014 : checkPrefixCuts (2^48) 3937927169 9 Manual.Count131072.C030014.packed 128 cuts30014 = true := by
 decide +kernel
def pointBounds30014 : List (Nat × Nat × Nat) := [(3937954816,105233998947711,105234382272394)]
theorem point_links_checked30014 : (cuts30014.take 1).map (fun c => (3937927169-1+2*2^9*c.k,105233908242533+c.lower,105234291567165+c.upper)) = pointBounds30014 := by
 decide +kernel
def cuts30015 : List PrefixCut := [⟨20,67186848,67186883⟩,
⟨128,422842402,422842634⟩]
theorem checked30015 : checkPrefixCuts (2^48) 3938058241 9 Manual.Count131072.C030015.packed 128 cuts30015 = true := by
 decide +kernel
def pointBounds30015 : List (Nat × Nat × Nat) := [(3938078720,105234403503613,105234786828514)]
theorem point_links_checked30015 : (cuts30015.take 1).map (fun c => (3938058241-1+2*2^9*c.k,105234336316765+c.lower,105234719641631+c.upper)) = pointBounds30015 := by
 decide +kernel
def cuts30016 : List PrefixCut := [⟨13,44170349,44170371⟩,
⟨128,421470317,421470556⟩]
theorem checked30016 : checkPrefixCuts (2^48) 3938189313 9 Manual.Count131072.C030016.packed 128 cuts30016 = true := by
 decide +kernel
def pointBounds30016 : List (Nat × Nat × Nat) := [(3938202624,105234803329516,105235186654636)]
theorem point_links_checked30016 : (cuts30016.take 1).map (fun c => (3938189313-1+2*2^9*c.k,105234759159167+c.lower,105235142484265+c.upper)) = pointBounds30016 := by
 decide +kernel
def cuts30017 : List PrefixCut := [⟨6,20011808,20011820⟩,
⟨127,421599249,421599485⟩,
⟨128,424672391,424672629⟩]
theorem checked30017 : checkPrefixCuts (2^48) 3938320385 9 Manual.Count131072.C030017.packed 128 cuts30017 = true := by
 decide +kernel
def pointBounds30017 : List (Nat × Nat × Nat) := [(3938326528,105235200641292,105235583966641),(3938450432,105235602228733,105235985554306)]
theorem point_links_checked30017 : (cuts30017.take 2).map (fun c => (3938320385-1+2*2^9*c.k,105235180629484+c.lower,105235563954821+c.upper)) = pointBounds30017 := by
 decide +kernel
def cuts30018 : List PrefixCut := [⟨120,394999746,394999970⟩,
⟨128,421871006,421871245⟩]
theorem checked30018 : checkPrefixCuts (2^48) 3938451457 9 Manual.Count131072.C030018.packed 128 cuts30018 = true := by
 decide +kernel
def pointBounds30018 : List (Nat × Nat × Nat) := [(3938574336,105236000301621,105236383627420)]
theorem point_links_checked30018 : (cuts30018.take 1).map (fun c => (3938451457-1+2*2^9*c.k,105235605301875+c.lower,105235988627450+c.upper)) = pointBounds30018 := by
 decide +kernel
def cuts30019 : List PrefixCut := [⟨113,378049821,378050023⟩,
⟨128,427645696,427645927⟩]
theorem checked30019 : checkPrefixCuts (2^48) 3938582529 9 Manual.Count131072.C030019.packed 128 cuts30019 = true := by
 decide +kernel
def pointBounds30019 : List (Nat × Nat × Nat) := [(3938698240,105236405222702,105236788548718)]
theorem point_links_checked30019 : (cuts30019.take 1).map (fun c => (3938582529-1+2*2^9*c.k,105236027172881+c.lower,105236410498695+c.upper)) = pointBounds30019 := by
 decide +kernel
def cuts30020 : List PrefixCut := [⟨106,354383455,354383649⟩,
⟨128,427631482,427631718⟩]
theorem checked30020 : checkPrefixCuts (2^48) 3938713601 9 Manual.Count131072.C030020.packed 128 cuts30020 = true := by
 decide +kernel
def pointBounds30020 : List (Nat × Nat × Nat) := [(3938822144,105236809202032,105237192528271)]
theorem point_links_checked30020 : (cuts30020.take 1).map (fun c => (3938713601-1+2*2^9*c.k,105236454818577+c.lower,105236838144622+c.upper)) = pointBounds30020 := by
 decide +kernel
def cuts30021 : List PrefixCut := [⟨99,326288045,326288229⟩,
⟨128,424044202,424044441⟩]
theorem checked30021 : checkPrefixCuts (2^48) 3938844673 9 Manual.Count131072.C030021.packed 128 cuts30021 = true := by
 decide +kernel
def pointBounds30021 : List (Nat × Nat × Nat) := [(3938946048,105237208738104,105237592064569)]
theorem point_links_checked30021 : (cuts30021.take 1).map (fun c => (3938844673-1+2*2^9*c.k,105236882450059+c.lower,105237265776340+c.upper)) = pointBounds30021 := by
 decide +kernel
def cuts30022 : List PrefixCut := [⟨92,309270482,309270654⟩,
⟨128,426245368,426245608⟩]
theorem checked30022 : checkPrefixCuts (2^48) 3938975745 9 Manual.Count131072.C030022.packed 128 cuts30022 = true := by
 decide +kernel
def pointBounds30022 : List (Nat × Nat × Nat) := [(3939069952,105237615764743,105237999091435)]
theorem point_links_checked30022 : (cuts30022.take 1).map (fun c => (3938975745-1+2*2^9*c.k,105237306494261+c.lower,105237689820781+c.upper)) = pointBounds30022 := by
 decide +kernel
def cuts30023 : List PrefixCut := [⟨85,280320825,280320982⟩,
⟨128,424015925,424016159⟩]
theorem checked30023 : checkPrefixCuts (2^48) 3939106817 9 Manual.Count131072.C030023.packed 128 cuts30023 = true := by
 decide +kernel
def pointBounds30023 : List (Nat × Nat × Nat) := [(3939193856,105238013060454,105238396387371)]
theorem point_links_checked30023 : (cuts30023.take 1).map (fun c => (3939106817-1+2*2^9*c.k,105237732739629+c.lower,105238116066389+c.upper)) = pointBounds30023 := by
 decide +kernel
def cuts30024 : List PrefixCut := [⟨78,258232668,258232816⟩,
⟨128,424144764,424145005⟩]
theorem checked30024 : checkPrefixCuts (2^48) 3939237889 9 Manual.Count131072.C030024.packed 128 cuts30024 = true := by
 decide +kernel
def pointBounds30024 : List (Nat × Nat × Nat) := [(3939317760,105238414988222,105238798315364)]
theorem point_links_checked30024 : (cuts30024.take 1).map (fun c => (3939237889-1+2*2^9*c.k,105238156755554+c.lower,105238540082548+c.upper)) = pointBounds30024 := by
 decide +kernel
def cuts30025 : List PrefixCut := [⟨71,239289778,239289910⟩,
⟨128,426274229,426274466⟩]
theorem checked30025 : checkPrefixCuts (2^48) 3939368961 9 Manual.Count131072.C030025.packed 128 cuts30025 = true := by
 decide +kernel
def pointBounds30025 : List (Nat × Nat × Nat) := [(3939441664,105238820190096,105239203517463)]
theorem point_links_checked30025 : (cuts30025.take 1).map (fun c => (3939368961-1+2*2^9*c.k,105238580900318+c.lower,105238964227553+c.upper)) = pointBounds30025 := by
 decide +kernel
def cuts30026 : List PrefixCut := [⟨64,212060062,212060181⟩,
⟨128,424116576,424116814⟩]
theorem checked30026 : checkPrefixCuts (2^48) 3939500033 9 Manual.Count131072.C030026.packed 128 cuts30026 = true := by
 decide +kernel
def pointBounds30026 : List (Nat × Nat × Nat) := [(3939565568,105239219234609,105239602562200)]
theorem point_links_checked30026 : (cuts30026.take 1).map (fun c => (3939500033-1+2*2^9*c.k,105239007174547+c.lower,105239390502019+c.upper)) = pointBounds30026 := by
 decide +kernel
def cuts30027 : List PrefixCut := [⟨57,189761904,189762008⟩,
⟨128,424888385,424888624⟩]
theorem checked30027 : checkPrefixCuts (2^48) 3939631105 9 Manual.Count131072.C030027.packed 128 cuts30027 = true := by
 decide +kernel
def pointBounds30027 : List (Nat × Nat × Nat) := [(3939689472,105239621053027,105240004380841)]
theorem point_links_checked30027 : (cuts30027.take 1).map (fun c => (3939631105-1+2*2^9*c.k,105239431291123+c.lower,105239814618833+c.upper)) = pointBounds30027 := by
 decide +kernel
def cuts30028 : List PrefixCut := [⟨50,168751156,168751244⟩,
⟨128,426088807,426089039⟩]
theorem checked30028 : checkPrefixCuts (2^48) 3939762177 9 Manual.Count131072.C030028.packed 128 cuts30028 = true := by
 decide +kernel
def pointBounds30028 : List (Nat × Nat × Nat) := [(3939813376,105240024930664,105240408258701)]
theorem point_links_checked30028 : (cuts30028.take 1).map (fun c => (3939762177-1+2*2^9*c.k,105239856179508+c.lower,105240239507457+c.upper)) = pointBounds30028 := by
 decide +kernel
def cuts30029 : List PrefixCut := [⟨43,143169490,143169570⟩,
⟨128,426431808,426432045⟩]
theorem checked30029 : checkPrefixCuts (2^48) 3939893249 9 Manual.Count131072.C030029.packed 128 cuts30029 = true := by
 decide +kernel
def pointBounds30029 : List (Nat × Nat × Nat) := [(3939937280,105240425437805,105240808766066)]
theorem point_links_checked30029 : (cuts30029.take 1).map (fun c => (3939893249-1+2*2^9*c.k,105240282268315+c.lower,105240665596496+c.upper)) = pointBounds30029 := by
 decide +kernel
def cuts30030 : List PrefixCut := [⟨36,121447244,121447309⟩,
⟨128,428417891,428418124⟩]
theorem checked30030 : checkPrefixCuts (2^48) 3940024321 9 Manual.Count131072.C030030.packed 128 cuts30030 = true := by
 decide +kernel
def pointBounds30030 : List (Nat × Nat × Nat) := [(3940061184,105240830147367,105241213475850)]
theorem point_links_checked30030 : (cuts30030.take 1).map (fun c => (3940024321-1+2*2^9*c.k,105240708700123+c.lower,105241092028541+c.upper)) = pointBounds30030 := by
 decide +kernel
def cuts30031 : List PrefixCut := [⟨29,92296915,92296971⟩,
⟨128,415473593,415473838⟩]
theorem checked30031 : checkPrefixCuts (2^48) 3940155393 9 Manual.Count131072.C030031.packed 128 cuts30031 = true := by
 decide +kernel
def pointBounds30031 : List (Nat × Nat × Nat) := [(3940185088,105241229414929,105241612743636)]
theorem point_links_checked30031 : (cuts30031.take 1).map (fun c => (3940155393-1+2*2^9*c.k,105241137118014+c.lower,105241520446665+c.upper)) = pointBounds30031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000000
