import PlattAssemblyKernel
import PlattCertificates.Count131072.C026048
import PlattCertificates.Count131072.C026049
import PlattCertificates.Count131072.C026050
import PlattCertificates.Count131072.C026051
import PlattCertificates.Count131072.C026052
import PlattCertificates.Count131072.C026053
import PlattCertificates.Count131072.C026054
import PlattCertificates.Count131072.C026055
import PlattCertificates.Count131072.C026056
import PlattCertificates.Count131072.C026057
import PlattCertificates.Count131072.C026058
import PlattCertificates.Count131072.C026059
import PlattCertificates.Count131072.C026060
import PlattCertificates.Count131072.C026061
import PlattCertificates.Count131072.C026062
import PlattCertificates.Count131072.C026063
import PlattCertificates.Count131072.C026064
import PlattCertificates.Count131072.C026065
import PlattCertificates.Count131072.C026066
import PlattCertificates.Count131072.C026067
import PlattCertificates.Count131072.C026068
import PlattCertificates.Count131072.C026069
import PlattCertificates.Count131072.C026070
import PlattCertificates.Count131072.C026071
import PlattCertificates.Count131072.C026072
import PlattCertificates.Count131072.C026073
import PlattCertificates.Count131072.C026074
import PlattCertificates.Count131072.C026075
import PlattCertificates.Count131072.C026076
import PlattCertificates.Count131072.C026077
import PlattCertificates.Count131072.C026078
import PlattCertificates.Count131072.C026079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26048 : List PrefixCut := [⟨61,234114521,234114650⟩,
⟨128,491528528,491528801⟩]
theorem checked26048 : checkPrefixCuts (2^48) 3418095617 9 Manual.Count131072.C026048.packed 128 cuts26048 = true := by
 decide +kernel
def pointBounds26048 : List (Nat × Nat × Nat) := [(3418158080,103424627640832,103425009952373)]
theorem point_links_checked26048 : (cuts26048.take 1).map (fun c => (3418095617-1+2*2^9*c.k,103424393526311+c.lower,103424775837723+c.upper)) = pointBounds26048 := by
 decide +kernel
def cuts26049 : List PrefixCut := [⟨38,146326765,146326851⟩,
⟨128,491097928,491098208⟩]
theorem checked26049 : checkPrefixCuts (2^48) 3418226689 9 Manual.Count131072.C026049.packed 128 cuts26049 = true := by
 decide +kernel
def pointBounds26049 : List (Nat × Nat × Nat) := [(3418265600,103425031381604,103425413693375)]
theorem point_links_checked26049 : (cuts26049.take 1).map (fun c => (3418226689-1+2*2^9*c.k,103424885054839+c.lower,103425267366524+c.upper)) = pointBounds26049 := by
 decide +kernel
def cuts26050 : List PrefixCut := [⟨15,61427099,61427134⟩,
⟨120,460778399,460778656⟩,
⟨128,491326200,491326474⟩]
theorem checked26050 : checkPrefixCuts (2^48) 3418357761 9 Manual.Count131072.C026050.packed 128 cuts26050 = true := by
 decide +kernel
def pointBounds26050 : List (Nat × Nat × Nat) := [(3418373120,103425437579866,103425819891866),(3418480640,103425836931166,103426219243388)]
theorem point_links_checked26050 : (cuts26050.take 2).map (fun c => (3418357761-1+2*2^9*c.k,103425376152767+c.lower,103425758464732+c.upper)) = pointBounds26050 := by
 decide +kernel
def cuts26051 : List PrefixCut := [⟨97,371261137,371261344⟩,
⟨128,492460047,492460324⟩]
theorem checked26051 : checkPrefixCuts (2^48) 3418488833 9 Manual.Count131072.C026051.packed 128 cuts26051 = true := by
 decide +kernel
def pointBounds26051 : List (Nat × Nat × Nat) := [(3418588160,103426238740104,103426621052550)]
theorem point_links_checked26051 : (cuts26051.take 1).map (fun c => (3418488833-1+2*2^9*c.k,103425867478967+c.lower,103426249791206+c.upper)) = pointBounds26051 := by
 decide +kernel
def cuts26052 : List PrefixCut := [⟨74,279444689,279444846⟩,
⟨128,488736030,488736302⟩]
theorem checked26052 : checkPrefixCuts (2^48) 3418619905 9 Manual.Count131072.C026052.packed 128 cuts26052 = true := by
 decide +kernel
def pointBounds26052 : List (Nat × Nat × Nat) := [(3418695680,103426639383703,103427021696376)]
theorem point_links_checked26052 : (cuts26052.take 1).map (fun c => (3418619905-1+2*2^9*c.k,103426359939014+c.lower,103426742251530+c.upper)) = pointBounds26052 := by
 decide +kernel
def cuts26053 : List PrefixCut := [⟨51,193233291,193233400⟩,
⟨128,486988370,486988642⟩]
theorem checked26053 : checkPrefixCuts (2^48) 3418750977 9 Manual.Count131072.C026053.packed 128 cuts26053 = true := by
 decide +kernel
def pointBounds26053 : List (Nat × Nat × Nat) := [(3418803200,103427041908335,103427424221232)]
theorem point_links_checked26053 : (cuts26053.take 1).map (fun c => (3418750977-1+2*2^9*c.k,103426848675044+c.lower,103427230987832+c.upper)) = pointBounds26053 := by
 decide +kernel
def cuts26054 : List PrefixCut := [⟨28,108262854,108262914⟩,
⟨128,486146460,486146732⟩]
theorem checked26054 : checkPrefixCuts (2^48) 3418882049 9 Manual.Count131072.C026054.packed 128 cuts26054 = true := by
 decide +kernel
def pointBounds26054 : List (Nat × Nat × Nat) := [(3418910720,103427443926268,103427826239388)]
theorem point_links_checked26054 : (cuts26054.take 1).map (fun c => (3418882049-1+2*2^9*c.k,103427335663414+c.lower,103427717976474+c.upper)) = pointBounds26054 := by
 decide +kernel
def cuts26055 : List PrefixCut := [⟨5,18605744,18605753⟩,
⟨110,421092433,421092665⟩,
⟨128,491149666,491149934⟩]
theorem checked26055 : checkPrefixCuts (2^48) 3419013121 9 Manual.Count131072.C026055.packed 128 cuts26055 = true := by
 decide +kernel
def pointBounds26055 : List (Nat × Nat × Nat) := [(3419018240,103427840415618,103428222728959),(3419125760,103428242902307,103428625215871)]
theorem point_links_checked26055 : (cuts26055.take 2).map (fun c => (3419013121-1+2*2^9*c.k,103427821809874+c.lower,103428204123206+c.upper)) = pointBounds26055 := by
 decide +kernel
def cuts26056 : List PrefixCut := [⟨87,330441067,330441256⟩,
⟨128,489978304,489978583⟩]
theorem checked26056 : checkPrefixCuts (2^48) 3419144193 9 Manual.Count131072.C026056.packed 128 cuts26056 = true := by
 decide +kernel
def pointBounds26056 : List (Nat × Nat × Nat) := [(3419233280,103428643400607,103429025714396)]
theorem point_links_checked26056 : (cuts26056.take 1).map (fun c => (3419144193-1+2*2^9*c.k,103428312959540+c.lower,103428695273140+c.upper)) = pointBounds26056 := by
 decide +kernel
def cuts26057 : List PrefixCut := [⟨64,245229047,245229186⟩,
⟨128,493499190,493499466⟩]
theorem checked26057 : checkPrefixCuts (2^48) 3419275265 9 Manual.Count131072.C026057.packed 128 cuts26057 = true := by
 decide +kernel
def pointBounds26057 : List (Nat × Nat × Nat) := [(3419340800,103429048166891,103429430480909)]
theorem point_links_checked26057 : (cuts26057.take 1).map (fun c => (3419275265-1+2*2^9*c.k,103428802937844+c.lower,103429185251723+c.upper)) = pointBounds26057 := by
 decide +kernel
def cuts26058 : List PrefixCut := [⟨41,163974238,163974331⟩,
⟨128,495455985,495456263⟩]
theorem checked26058 : checkPrefixCuts (2^48) 3419406337 9 Manual.Count131072.C026058.packed 128 cuts26058 = true := by
 decide +kernel
def pointBounds26058 : List (Nat × Nat × Nat) := [(3419448320,103429460411272,103429842725520)]
theorem point_links_checked26058 : (cuts26058.take 1).map (fun c => (3419406337-1+2*2^9*c.k,103429296437034+c.lower,103429678751189+c.upper)) = pointBounds26058 := by
 decide +kernel
def cuts26059 : List PrefixCut := [⟨18,69472607,69472646⟩,
⟨123,476011607,476011880⟩,
⟨128,494202259,494202542⟩]
theorem checked26059 : checkPrefixCuts (2^48) 3419537409 9 Manual.Count131072.C026059.packed 128 cuts26059 = true := by
 decide +kernel
def pointBounds26059 : List (Nat × Nat × Nat) := [(3419555840,103429861365626,103430243680098),(3419663360,103430267904626,103430650219332)]
theorem point_links_checked26059 : (cuts26059.take 2).map (fun c => (3419537409-1+2*2^9*c.k,103429791893019+c.lower,103430174207452+c.upper)) = pointBounds26059 := by
 decide +kernel
def cuts26060 : List PrefixCut := [⟨100,380927671,380927890⟩,
⟨128,489080093,489080370⟩]
theorem checked26060 : checkPrefixCuts (2^48) 3419668481 9 Manual.Count131072.C026060.packed 128 cuts26060 = true := by
 decide +kernel
def pointBounds26060 : List (Nat × Nat × Nat) := [(3419770880,103430667022949,103431049337884)]
theorem point_links_checked26060 : (cuts26060.take 1).map (fun c => (3419668481-1+2*2^9*c.k,103430286095278+c.lower,103430668409994+c.upper)) = pointBounds26060 := by
 decide +kernel
def cuts26061 : List PrefixCut := [⟨77,295397977,295398146⟩,
⟨128,493670476,493670758⟩]
theorem checked26061 : checkPrefixCuts (2^48) 3419799553 9 Manual.Count131072.C026061.packed 128 cuts26061 = true := by
 decide +kernel
def pointBounds26061 : List (Nat × Nat × Nat) := [(3419878400,103431070573348,103431452888510)]
theorem point_links_checked26061 : (cuts26061.take 1).map (fun c => (3419799553-1+2*2^9*c.k,103430775175371+c.lower,103431157490364+c.upper)) = pointBounds26061 := by
 decide +kernel
def cuts26062 : List PrefixCut := [⟨54,206335125,206335241⟩,
⟨128,490277106,490277383⟩]
theorem checked26062 : checkPrefixCuts (2^48) 3419930625 9 Manual.Count131072.C026062.packed 128 cuts26062 = true := by
 decide +kernel
def pointBounds26062 : List (Nat × Nat × Nat) := [(3419985920,103431475180972,103431857496363)]
theorem point_links_checked26062 : (cuts26062.take 1).map (fun c => (3419930625-1+2*2^9*c.k,103431268845847+c.lower,103431651161122+c.upper)) = pointBounds26062 := by
 decide +kernel
def cuts26063 : List PrefixCut := [⟨31,118019258,118019326⟩,
⟨128,490669830,490670106⟩]
theorem checked26063 : checkPrefixCuts (2^48) 3420061697 9 Manual.Count131072.C026063.packed 128 cuts26063 = true := by
 decide +kernel
def pointBounds26063 : List (Nat × Nat × Nat) := [(3420093440,103431877142211,103432259457831)]
theorem point_links_checked26063 : (cuts26063.take 1).map (fun c => (3420061697-1+2*2^9*c.k,103431759122953+c.lower,103432141438505+c.upper)) = pointBounds26063 := by
 decide +kernel
def cuts26064 : List PrefixCut := [⟨8,32178465,32178484⟩,
⟨113,436830173,436830419⟩,
⟨128,494272079,494272357⟩]
theorem checked26064 : checkPrefixCuts (2^48) 3420192769 9 Manual.Count131072.C026064.packed 128 cuts26064 = true := by
 decide +kernel
def pointBounds26064 : List (Nat × Nat × Nat) := [(3420200960,103432281971248,103432664287095),(3420308480,103432686622956,103433068939030)]
theorem point_links_checked26064 : (cuts26064.take 2).map (fun c => (3420192769-1+2*2^9*c.k,103432249792783+c.lower,103432632108611+c.upper)) = pointBounds26064 := by
 decide +kernel
def cuts26065 : List PrefixCut := [⟨90,344810601,344810796⟩,
⟨128,491702048,491702325⟩]
theorem checked26065 : checkPrefixCuts (2^48) 3420323841 9 Manual.Count131072.C026065.packed 128 cuts26065 = true := by
 decide +kernel
def pointBounds26065 : List (Nat × Nat × Nat) := [(3420416000,103433088875463,103433471191764)]
theorem point_links_checked26065 : (cuts26065.take 1).map (fun c => (3420323841-1+2*2^9*c.k,103432744064862+c.lower,103433126380968+c.upper)) = pointBounds26065 := by
 decide +kernel
def cuts26066 : List PrefixCut := [⟨67,253867228,253867372⟩,
⟨128,491189454,491189729⟩]
theorem checked26066 : checkPrefixCuts (2^48) 3420454913 9 Manual.Count131072.C026066.packed 128 cuts26066 = true := by
 decide +kernel
def pointBounds26066 : List (Nat × Nat × Nat) := [(3420523520,103433489634138,103433871950665)]
theorem point_links_checked26066 : (cuts26066.take 1).map (fun c => (3420454913-1+2*2^9*c.k,103433235766910+c.lower,103433618083293+c.upper)) = pointBounds26066 := by
 decide +kernel
def cuts26067 : List PrefixCut := [⟨44,167209139,167209240⟩,
⟨128,494462109,494462394⟩]
theorem checked26067 : checkPrefixCuts (2^48) 3420585985 9 Manual.Count131072.C026067.packed 128 cuts26067 = true := by
 decide +kernel
def pointBounds26067 : List (Nat × Nat × Nat) := [(3420631040,103433894165503,103434276482262)]
theorem point_links_checked26067 : (cuts26067.take 1).map (fun c => (3420585985-1+2*2^9*c.k,103433726956364+c.lower,103434109273022+c.upper)) = pointBounds26067 := by
 decide +kernel
def cuts26068 : List PrefixCut := [⟨21,83107944,83107987⟩,
⟨126,488930340,488930609⟩,
⟨128,497158562,497158836⟩]
theorem checked26068 : checkPrefixCuts (2^48) 3420717057 9 Manual.Count131072.C026068.packed 128 cuts26068 = true := by
 decide +kernel
def pointBounds26068 : List (Nat × Nat × Nat) := [(3420738560,103434304526417,103434686843403),(3420846080,103434710348813,103435092666025)]
theorem point_links_checked26068 : (cuts26068.take 2).map (fun c => (3420717057-1+2*2^9*c.k,103434221418473+c.lower,103434603735416+c.upper)) = pointBounds26068 := by
 decide +kernel
def cuts26069 : List PrefixCut := [⟨103,395277567,395277783⟩,
⟨128,491462142,491462413⟩]
theorem checked26069 : checkPrefixCuts (2^48) 3420848129 9 Manual.Count131072.C026069.packed 128 cuts26069 = true := by
 decide +kernel
def pointBounds26069 : List (Nat × Nat × Nat) := [(3420953600,103435113854602,103435496172035)]
theorem point_links_checked26069 : (cuts26069.take 1).map (fun c => (3420848129-1+2*2^9*c.k,103434718577035+c.lower,103435100894252+c.upper)) = pointBounds26069 := by
 decide +kernel
def cuts26070 : List PrefixCut := [⟨80,313397115,313397295⟩,
⟨128,497778709,497778994⟩]
theorem checked26070 : checkPrefixCuts (2^48) 3420979201 9 Manual.Count131072.C026070.packed 128 cuts26070 = true := by
 decide +kernel
def pointBounds26070 : List (Nat × Nat × Nat) := [(3421061120,103435523436292,103435905753960)]
theorem point_links_checked26070 : (cuts26070.take 1).map (fun c => (3420979201-1+2*2^9*c.k,103435210039177+c.lower,103435592356665+c.upper)) = pointBounds26070 := by
 decide +kernel
def cuts26071 : List PrefixCut := [⟨57,218605192,218605316⟩,
⟨128,485418520,485418795⟩]
theorem checked26071 : checkPrefixCuts (2^48) 3421110273 9 Manual.Count131072.C026071.packed 128 cuts26071 = true := by
 decide +kernel
def pointBounds26071 : List (Nat × Nat × Nat) := [(3421168640,103435926423078,103436308740975)]
theorem point_links_checked26071 : (cuts26071.take 1).map (fun c => (3421110273-1+2*2^9*c.k,103435707817886+c.lower,103436090135659+c.upper)) = pointBounds26071 := by
 decide +kernel
def cuts26072 : List PrefixCut := [⟨34,130072539,130072615⟩,
⟨128,485399912,485400187⟩]
theorem checked26072 : checkPrefixCuts (2^48) 3421241345 9 Manual.Count131072.C026072.packed 128 cuts26072 = true := by
 decide +kernel
def pointBounds26072 : List (Nat × Nat × Nat) := [(3421276160,103436323308945,103436705627069)]
theorem point_links_checked26072 : (cuts26072.take 1).map (fun c => (3421241345-1+2*2^9*c.k,103436193236406+c.lower,103436575554454+c.upper)) = pointBounds26072 := by
 decide +kernel
def cuts26073 : List PrefixCut := [⟨11,43931888,43931910⟩,
⟨116,443096376,443096621⟩,
⟨128,489330195,489330466⟩]
theorem checked26073 : checkPrefixCuts (2^48) 3421372417 9 Manual.Count131072.C026073.packed 128 cuts26073 = true := by
 decide +kernel
def pointBounds26073 : List (Nat × Nat × Nat) := [(3421383680,103436722568206,103437104886551),(3421491200,103437121732694,103437504051262)]
theorem point_links_checked26073 : (cuts26073.take 2).map (fun c => (3421372417-1+2*2^9*c.k,103436678636318+c.lower,103437060954641+c.upper)) = pointBounds26073 := by
 decide +kernel
def cuts26074 : List PrefixCut := [⟨93,361226929,361227128⟩,
⟨128,496962066,496962344⟩]
theorem checked26074 : checkPrefixCuts (2^48) 3421503489 9 Manual.Count131072.C026074.packed 128 cuts26074 = true := by
 decide +kernel
def pointBounds26074 : List (Nat × Nat × Nat) := [(3421598720,103437529193442,103437911512235)]
theorem point_links_checked26074 : (cuts26074.take 1).map (fun c => (3421503489-1+2*2^9*c.k,103437167966513+c.lower,103437550285107+c.upper)) = pointBounds26074 := by
 decide +kernel
def cuts26075 : List PrefixCut := [⟨70,269985279,269985427⟩,
⟨128,492171803,492172077⟩]
theorem checked26075 : checkPrefixCuts (2^48) 3421634561 9 Manual.Count131072.C026075.packed 128 cuts26075 = true := by
 decide +kernel
def pointBounds26075 : List (Nat × Nat × Nat) := [(3421706240,103437934913858,103438317232878)]
theorem point_links_checked26075 : (cuts26075.take 1).map (fun c => (3421634561-1+2*2^9*c.k,103437664928579+c.lower,103438047247451+c.upper)) = pointBounds26075 := by
 decide +kernel
def cuts26076 : List PrefixCut := [⟨47,181629085,181629190⟩,
⟨128,493551376,493551653⟩]
theorem checked26076 : checkPrefixCuts (2^48) 3421765633 9 Manual.Count131072.C026076.packed 128 cuts26076 = true := by
 decide +kernel
def pointBounds26076 : List (Nat × Nat × Nat) := [(3421813760,103438338729467,103438721048718)]
theorem point_links_checked26076 : (cuts26076.take 1).map (fun c => (3421765633-1+2*2^9*c.k,103438157100382+c.lower,103438539419528+c.upper)) = pointBounds26076 := by
 decide +kernel
def cuts26077 : List PrefixCut := [⟨24,91716208,91716259⟩,
⟨128,496575917,496576190⟩]
theorem checked26077 : checkPrefixCuts (2^48) 3421896705 9 Manual.Count131072.C026077.packed 128 cuts26077 = true := by
 decide +kernel
def pointBounds26077 : List (Nat × Nat × Nat) := [(3421921280,103438742367966,103439124687440)]
theorem point_links_checked26077 : (cuts26077.take 1).map (fun c => (3421896705-1+2*2^9*c.k,103438650651758+c.lower,103439032971181+c.upper)) = pointBounds26077 := by
 decide +kernel
def cuts26078 : List PrefixCut := [⟨1,3701422,3701424⟩,
⟨106,407479007,407479234⟩,
⟨128,491374979,491375253⟩]
theorem checked26078 : checkPrefixCuts (2^48) 3422027777 9 Manual.Count131072.C026078.packed 128 cuts26078 = true := by
 decide +kernel
def pointBounds26078 : List (Nat × Nat × Nat) := [(3422028800,103439150929097,103439533248795),(3422136320,103439554706682,103439937026605)]
theorem point_links_checked26078 : (cuts26078.take 2).map (fun c => (3422027777-1+2*2^9*c.k,103439147227675+c.lower,103439529547371+c.upper)) = pointBounds26078 := by
 decide +kernel
def cuts26079 : List PrefixCut := [⟨83,316414413,316414588⟩,
⟨128,490040108,490040382⟩]
theorem checked26079 : checkPrefixCuts (2^48) 3422158849 9 Manual.Count131072.C026079.packed 128 cuts26079 = true := by
 decide +kernel
def pointBounds26079 : List (Nat × Nat × Nat) := [(3422243840,103439955017067,103440337337212)]
theorem point_links_checked26079 : (cuts26079.take 1).map (fun c => (3422158849-1+2*2^9*c.k,103439638602654+c.lower,103440020922624+c.upper)) = pointBounds26079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000189
