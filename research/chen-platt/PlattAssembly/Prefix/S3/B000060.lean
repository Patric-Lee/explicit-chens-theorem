import PlattAssemblyKernel
import PlattCertificates.Count131072.C021920
import PlattCertificates.Count131072.C021921
import PlattCertificates.Count131072.C021922
import PlattCertificates.Count131072.C021923
import PlattCertificates.Count131072.C021924
import PlattCertificates.Count131072.C021925
import PlattCertificates.Count131072.C021926
import PlattCertificates.Count131072.C021927
import PlattCertificates.Count131072.C021928
import PlattCertificates.Count131072.C021929
import PlattCertificates.Count131072.C021930
import PlattCertificates.Count131072.C021931
import PlattCertificates.Count131072.C021932
import PlattCertificates.Count131072.C021933
import PlattCertificates.Count131072.C021934
import PlattCertificates.Count131072.C021935
import PlattCertificates.Count131072.C021936
import PlattCertificates.Count131072.C021937
import PlattCertificates.Count131072.C021938
import PlattCertificates.Count131072.C021939
import PlattCertificates.Count131072.C021940
import PlattCertificates.Count131072.C021941
import PlattCertificates.Count131072.C021942
import PlattCertificates.Count131072.C021943
import PlattCertificates.Count131072.C021944
import PlattCertificates.Count131072.C021945
import PlattCertificates.Count131072.C021946
import PlattCertificates.Count131072.C021947
import PlattCertificates.Count131072.C021948
import PlattCertificates.Count131072.C021949
import PlattCertificates.Count131072.C021950
import PlattCertificates.Count131072.C021951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21920 : List PrefixCut := [⟨34,158785609,158785695⟩,
⟨122,563714396,563714714⟩,
⟨128,591302700,591303034⟩]
theorem checked21920 : checkPrefixCuts (2^48) 2877030401 9 Manual.Count131072.C021920.packed 128 cuts21920 = true := by
 decide +kernel
def pointBounds21920 : List (Nat × Nat × Nat) := [(2877065216,101206441212490,101206822269908),(2877155328,101206846141277,101207227198927)]
theorem point_links_checked21920 : (cuts21920.take 2).map (fun c => (2877030401-1+2*2^9*c.k,101206282426881+c.lower,101206663484213+c.upper)) = pointBounds21920 := by
 decide +kernel
def cuts21921 : List PrefixCut := [⟨82,375371141,375371358⟩,
⟨128,584329814,584330155⟩]
theorem checked21921 : checkPrefixCuts (2^48) 2877161473 9 Manual.Count131072.C021921.packed 128 cuts21921 = true := by
 decide +kernel
def pointBounds21921 : List (Nat × Nat × Nat) := [(2877245440,101207249100722,101207630158605)]
theorem point_links_checked21921 : (cuts21921.take 1).map (fun c => (2877161473-1+2*2^9*c.k,101206873729581+c.lower,101207254787247+c.upper)) = pointBounds21921 := by
 decide +kernel
def cuts21922 : List PrefixCut := [⟨42,190662059,190662169⟩,
⟨128,579803401,579803734⟩]
theorem checked21922 : checkPrefixCuts (2^48) 2877292545 9 Manual.Count131072.C021922.packed 128 cuts21922 = true := by
 decide +kernel
def pointBounds21922 : List (Nat × Nat × Nat) := [(2877335552,101207648721454,101208029779571)]
theorem point_links_checked21922 : (cuts21922.take 1).map (fun c => (2877292545-1+2*2^9*c.k,101207458059395+c.lower,101207839117402+c.upper)) = pointBounds21922 := by
 decide +kernel
def cuts21923 : List PrefixCut := [⟨2,9880003,9880009⟩,
⟨90,412801633,412801870⟩,
⟨128,590928302,590928637⟩]
theorem checked21923 : checkPrefixCuts (2^48) 2877423617 9 Manual.Count131072.C021923.packed 128 cuts21923 = true := by
 decide +kernel
def pointBounds21923 : List (Nat × Nat × Nat) := [(2877425664,101208047742799,101208428801145),(2877515776,101208450664429,101208831723006)]
theorem point_links_checked21923 : (cuts21923.take 2).map (fun c => (2877423617-1+2*2^9*c.k,101208037862796+c.lower,101208418921136+c.upper)) = pointBounds21923 := by
 decide +kernel
def cuts21924 : List PrefixCut := [⟨50,222043546,222043673⟩,
⟨128,581119855,581120186⟩]
theorem checked21924 : checkPrefixCuts (2^48) 2877554689 9 Manual.Count131072.C021924.packed 128 cuts21924 = true := by
 decide +kernel
def pointBounds21924 : List (Nat × Nat × Nat) := [(2877605888,101208850834644,101209231893446)]
theorem point_links_checked21924 : (cuts21924.take 1).map (fun c => (2877554689-1+2*2^9*c.k,101208628791098+c.lower,101209009849773+c.upper)) = pointBounds21924 := by
 decide +kernel
def cuts21925 : List PrefixCut := [⟨10,46558872,46558901⟩,
⟨98,452963819,452964080⟩,
⟨128,591265745,591266087⟩]
theorem checked21925 : checkPrefixCuts (2^48) 2877685761 9 Manual.Count131072.C021925.packed 128 cuts21925 = true := by
 decide +kernel
def pointBounds21925 : List (Nat × Nat × Nat) := [(2877696000,101209256469825,101209637528860),(2877786112,101209662874772,101210043934039)]
theorem point_links_checked21925 : (cuts21925.take 2).map (fun c => (2877685761-1+2*2^9*c.k,101209209910953+c.lower,101209590969959+c.upper)) = pointBounds21925 := by
 decide +kernel
def cuts21926 : List PrefixCut := [⟨58,266329774,266329929⟩,
⟨128,591923500,591923845⟩]
theorem checked21926 : checkPrefixCuts (2^48) 2877816833 9 Manual.Count131072.C021926.packed 128 cuts21926 = true := by
 decide +kernel
def pointBounds21926 : List (Nat × Nat × Nat) := [(2877876224,101210067506472,101210448565975)]
theorem point_links_checked21926 : (cuts21926.take 1).map (fun c => (2877816833-1+2*2^9*c.k,101209801176698+c.lower,101210182236046+c.upper)) = pointBounds21926 := by
 decide +kernel
def cuts21927 : List PrefixCut := [⟨18,82937555,82937603⟩,
⟨106,484903255,484903528⟩,
⟨128,591505203,591505535⟩]
theorem checked21927 : checkPrefixCuts (2^48) 2877947905 9 Manual.Count131072.C021927.packed 128 cuts21927 = true := by
 decide +kernel
def pointBounds21927 : List (Nat × Nat × Nat) := [(2877966336,101210476037753,101210857097494),(2878056448,101210878003453,101211259063419)]
theorem point_links_checked21927 : (cuts21927.take 2).map (fun c => (2877947905-1+2*2^9*c.k,101210393100198+c.lower,101210774159891+c.upper)) = pointBounds21927 := by
 decide +kernel
def cuts21928 : List PrefixCut := [⟨66,303859726,303859898⟩,
⟨128,587468726,587469061⟩]
theorem checked21928 : checkPrefixCuts (2^48) 2878078977 9 Manual.Count131072.C021928.packed 128 cuts21928 = true := by
 decide +kernel
def pointBounds21928 : List (Nat × Nat × Nat) := [(2878146560,101211288465127,101211669525324)]
theorem point_links_checked21928 : (cuts21928.take 1).map (fun c => (2878078977-1+2*2^9*c.k,101210984605401+c.lower,101211365665426+c.upper)) = pointBounds21928 := by
 decide +kernel
def cuts21929 : List PrefixCut := [⟨26,119798473,119798537⟩,
⟨114,527300645,527300941⟩,
⟨128,593407300,593407633⟩]
theorem checked21929 : checkPrefixCuts (2^48) 2878210049 9 Manual.Count131072.C021929.packed 128 cuts21929 = true := by
 decide +kernel
def pointBounds21929 : List (Nat × Nat × Nat) := [(2878236672,101211691872600,101212072933024),(2878326784,101212099374772,101212480435428)]
theorem point_links_checked21929 : (cuts21929.take 2).map (fun c => (2878210049-1+2*2^9*c.k,101211572074127+c.lower,101211953134487+c.upper)) = pointBounds21929 := by
 decide +kernel
def cuts21930 : List PrefixCut := [⟨74,339133610,339133803⟩,
⟨128,584970507,584970846⟩]
theorem checked21930 : checkPrefixCuts (2^48) 2878341121 9 Manual.Count131072.C021930.packed 128 cuts21930 = true := by
 decide +kernel
def pointBounds21930 : List (Nat × Nat × Nat) := [(2878416896,101212504615037,101212885675923)]
theorem point_links_checked21930 : (cuts21930.take 1).map (fun c => (2878341121-1+2*2^9*c.k,101212165481427+c.lower,101212546542120+c.upper)) = pointBounds21930 := by
 decide +kernel
def cuts21931 : List PrefixCut := [⟨34,153523433,153523526⟩,
⟨122,559324953,559325277⟩,
⟨128,588268387,588268726⟩]
theorem checked21931 : checkPrefixCuts (2^48) 2878472193 9 Manual.Count131072.C021931.packed 128 cuts21931 = true := by
 decide +kernel
def pointBounds21931 : List (Nat × Nat × Nat) := [(2878507008,101212903975367,101213285036492),(2878597120,101213309776887,101213690838243)]
theorem point_links_checked21931 : (cuts21931.take 2).map (fun c => (2878472193-1+2*2^9*c.k,101212750451934+c.lower,101213131512966+c.upper)) = pointBounds21931 := by
 decide +kernel
def cuts21932 : List PrefixCut := [⟨82,380756659,380756878⟩,
⟨128,594890731,594891069⟩]
theorem checked21932 : checkPrefixCuts (2^48) 2878603265 9 Manual.Count131072.C021932.packed 128 cuts21932 = true := by
 decide +kernel
def pointBounds21932 : List (Nat × Nat × Nat) := [(2878687232,101213719476980,101214100538570)]
theorem point_links_checked21932 : (cuts21932.take 1).map (fun c => (2878603265-1+2*2^9*c.k,101213338720321+c.lower,101213719781692+c.upper)) = pointBounds21932 := by
 decide +kernel
def cuts21933 : List PrefixCut := [⟨42,194770947,194771057⟩,
⟨128,585770577,585770912⟩]
theorem checked21933 : checkPrefixCuts (2^48) 2878734337 9 Manual.Count131072.C021933.packed 128 cuts21933 = true := by
 decide +kernel
def pointBounds21933 : List (Nat × Nat × Nat) := [(2878777344,101214128381999,101214509443818)]
theorem point_links_checked21933 : (cuts21933.take 1).map (fun c => (2878734337-1+2*2^9*c.k,101213933611052+c.lower,101214314672761+c.upper)) = pointBounds21933 := by
 decide +kernel
def cuts21934 : List PrefixCut := [⟨2,9972828,9972834⟩,
⟨90,422078685,422078927⟩,
⟨128,587895026,587895367⟩]
theorem checked21934 : checkPrefixCuts (2^48) 2878865409 9 Manual.Count131072.C021934.packed 128 cuts21934 = true := by
 decide +kernel
def pointBounds21934 : List (Nat × Nat × Nat) := [(2878867456,101214529354457,101214910416507),(2878957568,101214941460314,101215322522600)]
theorem point_links_checked21934 : (cuts21934.take 2).map (fun c => (2878865409-1+2*2^9*c.k,101214519381629+c.lower,101214900443673+c.upper)) = pointBounds21934 := by
 decide +kernel
def cuts21935 : List PrefixCut := [⟨50,229851479,229851611⟩,
⟨128,586010548,586010881⟩]
theorem checked21935 : checkPrefixCuts (2^48) 2878996481 9 Manual.Count131072.C021935.packed 128 cuts21935 = true := by
 decide +kernel
def pointBounds21935 : List (Nat × Nat × Nat) := [(2879047680,101215337128134,101215718190651)]
theorem point_links_checked21935 : (cuts21935.take 1).map (fun c => (2878996481-1+2*2^9*c.k,101215107276655+c.lower,101215488339040+c.upper)) = pointBounds21935 := by
 decide +kernel
def cuts21936 : List PrefixCut := [⟨10,45851213,45851241⟩,
⟨98,451563781,451564042⟩,
⟨128,587450215,587450553⟩]
theorem checked21936 : checkPrefixCuts (2^48) 2879127553 9 Manual.Count131072.C021936.packed 128 cuts21936 = true := by
 decide +kernel
def pointBounds21936 : List (Nat × Nat × Nat) := [(2879137792,101215739138416,101216120201162),(2879227904,101216144850984,101216525913963)]
theorem point_links_checked21936 : (cuts21936.take 2).map (fun c => (2879127553-1+2*2^9*c.k,101215693287203+c.lower,101216074349921+c.upper)) = pointBounds21936 := by
 decide +kernel
def cuts21937 : List PrefixCut := [⟨58,265218792,265218944⟩,
⟨128,589085308,589085646⟩]
theorem checked21937 : checkPrefixCuts (2^48) 2879258625 9 Manual.Count131072.C021937.packed 128 cuts21937 = true := by
 decide +kernel
def pointBounds21937 : List (Nat × Nat × Nat) := [(2879318016,101216545956210,101216927019418)]
theorem point_links_checked21937 : (cuts21937.take 1).map (fun c => (2879258625-1+2*2^9*c.k,101216280737418+c.lower,101216661800474+c.upper)) = pointBounds21937 := by
 decide +kernel
def cuts21938 : List PrefixCut := [⟨18,86219687,86219737⟩,
⟨106,488961561,488961847⟩,
⟨128,588276559,588276898⟩]
theorem checked21938 : checkPrefixCuts (2^48) 2879389697 9 Manual.Count131072.C021938.packed 128 cuts21938 = true := by
 decide +kernel
def pointBounds21938 : List (Nat × Nat × Nat) := [(2879408128,101216956042413,101217337105857),(2879498240,101217358784287,101217739847967)]
theorem point_links_checked21938 : (cuts21938.take 2).map (fun c => (2879389697-1+2*2^9*c.k,101216869822726+c.lower,101217250886120+c.upper)) = pointBounds21938 := by
 decide +kernel
def cuts21939 : List PrefixCut := [⟨66,300090834,300091005⟩,
⟨128,589324901,589325238⟩]
theorem checked21939 : checkPrefixCuts (2^48) 2879520769 9 Manual.Count131072.C021939.packed 128 cuts21939 = true := by
 decide +kernel
def pointBounds21939 : List (Nat × Nat × Nat) := [(2879588352,101217758190119,101218139254023)]
theorem point_links_checked21939 : (cuts21939.take 1).map (fun c => (2879520769-1+2*2^9*c.k,101217458099285+c.lower,101217839163018+c.upper)) = pointBounds21939 := by
 decide +kernel
def cuts21940 : List PrefixCut := [⟨26,122084394,122084463⟩,
⟨114,530359850,530360153⟩,
⟨128,593696636,593696975⟩]
theorem checked21940 : checkPrefixCuts (2^48) 2879651841 9 Manual.Count131072.C021940.packed 128 cuts21940 = true := by
 decide +kernel
def pointBounds21940 : List (Nat × Nat × Nat) := [(2879678464,101218169508580,101218550572719),(2879768576,101218577784036,101218958848409)]
theorem point_links_checked21940 : (cuts21940.take 2).map (fun c => (2879651841-1+2*2^9*c.k,101218047424186+c.lower,101218428488256+c.upper)) = pointBounds21940 := by
 decide +kernel
def cuts21941 : List PrefixCut := [⟨74,336227035,336227234⟩,
⟨128,581452247,581452584⟩]
theorem checked21941 : checkPrefixCuts (2^48) 2879782913 9 Manual.Count131072.C021941.packed 128 cuts21941 = true := by
 decide +kernel
def pointBounds21941 : List (Nat × Nat × Nat) := [(2879858688,101218977347857,101219358412465)]
theorem point_links_checked21941 : (cuts21941.take 1).map (fun c => (2879782913-1+2*2^9*c.k,101218641120822+c.lower,101219022185231+c.upper)) = pointBounds21941 := by
 decide +kernel
def cuts21942 : List PrefixCut := [⟨34,153642054,153642140⟩,
⟨122,562563450,562563771⟩,
⟨128,589440001,589440336⟩]
theorem checked21942 : checkPrefixCuts (2^48) 2879913985 9 Manual.Count131072.C021942.packed 128 cuts21942 = true := by
 decide +kernel
def pointBounds21942 : List (Nat × Nat × Nat) := [(2879948800,101219376215123,101219757279955),(2880038912,101219785136519,101220166201586)]
theorem point_links_checked21942 : (cuts21942.take 2).map (fun c => (2879913985-1+2*2^9*c.k,101219222573069+c.lower,101219603637815+c.upper)) = pointBounds21942 := by
 decide +kernel
def cuts21943 : List PrefixCut := [⟨82,371086088,371086307⟩,
⟨128,585894761,585895099⟩]
theorem checked21943 : checkPrefixCuts (2^48) 2880045057 9 Manual.Count131072.C021943.packed 128 cuts21943 = true := by
 decide +kernel
def pointBounds21943 : List (Nat × Nat × Nat) := [(2880129024,101220183099158,101220564164458)]
theorem point_links_checked21943 : (cuts21943.take 1).map (fun c => (2880045057-1+2*2^9*c.k,101219812013070+c.lower,101220193078151+c.upper)) = pointBounds21943 := by
 decide +kernel
def cuts21944 : List PrefixCut := [⟨42,191448431,191448544⟩,
⟨128,586161386,586161730⟩]
theorem checked21944 : checkPrefixCuts (2^48) 2880176129 9 Manual.Count131072.C021944.packed 128 cuts21944 = true := by
 decide +kernel
def pointBounds21944 : List (Nat × Nat × Nat) := [(2880219136,101220589356262,101220970421794)]
theorem point_links_checked21944 : (cuts21944.take 1).map (fun c => (2880176129-1+2*2^9*c.k,101220397907831+c.lower,101220778973250+c.upper)) = pointBounds21944 := by
 decide +kernel
def cuts21945 : List PrefixCut := [⟨2,9381492,9381498⟩,
⟨90,418544812,418545049⟩,
⟨128,588577828,588578165⟩]
theorem checked21945 : checkPrefixCuts (2^48) 2880307201 9 Manual.Count131072.C021945.packed 128 cuts21945 = true := by
 decide +kernel
def pointBounds21945 : List (Nat × Nat × Nat) := [(2880309248,101220993450709,101221374516478),(2880399360,101221402614029,101221783680029)]
theorem point_links_checked21945 : (cuts21945.take 2).map (fun c => (2880307201-1+2*2^9*c.k,101220984069217+c.lower,101221365134980+c.upper)) = pointBounds21945 := by
 decide +kernel
def cuts21946 : List PrefixCut := [⟨50,225534540,225534667⟩,
⟨128,579854169,579854502⟩]
theorem checked21946 : checkPrefixCuts (2^48) 2880438273 9 Manual.Count131072.C021946.packed 128 cuts21946 = true := by
 decide +kernel
def pointBounds21946 : List (Nat × Nat × Nat) := [(2880489472,101221798181585,101222179247812)]
theorem point_links_checked21946 : (cuts21946.take 1).map (fun c => (2880438273-1+2*2^9*c.k,101221572647045+c.lower,101221953713145+c.upper)) = pointBounds21946 := by
 decide +kernel
def cuts21947 : List PrefixCut := [⟨10,44948829,44948856⟩,
⟨98,450360675,450360939⟩,
⟨128,587253930,587254271⟩]
theorem checked21947 : checkPrefixCuts (2^48) 2880569345 9 Manual.Count131072.C021947.packed 128 cuts21947 = true := by
 decide +kernel
def pointBounds21947 : List (Nat × Nat × Nat) := [(2880579584,101222197450043,101222578516503),(2880669696,101222602861889,101222983928586)]
theorem point_links_checked21947 : (cuts21947.take 2).map (fun c => (2880569345-1+2*2^9*c.k,101222152501214+c.lower,101222533567647+c.upper)) = pointBounds21947 := by
 decide +kernel
def cuts21948 : List PrefixCut := [⟨58,271046316,271046469⟩,
⟨128,589279125,589279462⟩]
theorem checked21948 : checkPrefixCuts (2^48) 2880700417 9 Manual.Count131072.C021948.packed 128 cuts21948 = true := by
 decide +kernel
def pointBounds21948 : List (Nat × Nat × Nat) := [(2880759808,101223010801460,101223391868387)]
theorem point_links_checked21948 : (cuts21948.take 1).map (fun c => (2880700417-1+2*2^9*c.k,101222739755144+c.lower,101223120821918+c.upper)) = pointBounds21948 := by
 decide +kernel
def cuts21949 : List PrefixCut := [⟨18,83049945,83049995⟩,
⟨106,494481369,494481654⟩,
⟨128,598240968,598241312⟩]
theorem checked21949 : checkPrefixCuts (2^48) 2880831489 9 Manual.Count131072.C021949.packed 128 cuts21949 = true := by
 decide +kernel
def pointBounds21949 : List (Nat × Nat × Nat) := [(2880849920,101223412084214,101223793151375),(2880940032,101223823515638,101224204583034)]
theorem point_links_checked21949 : (cuts21949.take 2).map (fun c => (2880831489-1+2*2^9*c.k,101223329034269+c.lower,101223710101380+c.upper)) = pointBounds21949 := by
 decide +kernel
def cuts21950 : List PrefixCut := [⟨66,304337181,304337360⟩,
⟨128,591863318,591863659⟩]
theorem checked21950 : checkPrefixCuts (2^48) 2880962561 9 Manual.Count131072.C021950.packed 128 cuts21950 = true := by
 decide +kernel
def pointBounds21950 : List (Nat × Nat × Nat) := [(2881030144,101224231612418,101224612680052)]
theorem point_links_checked21950 : (cuts21950.take 1).map (fun c => (2880962561-1+2*2^9*c.k,101223927275237+c.lower,101224308342692+c.upper)) = pointBounds21950 := by
 decide +kernel
def cuts21951 : List PrefixCut := [⟨26,117431538,117431604⟩,
⟨114,523744214,523744510⟩,
⟨128,588905476,588905807⟩]
theorem checked21951 : checkPrefixCuts (2^48) 2881093633 9 Manual.Count131072.C021951.packed 128 cuts21951 = true := by
 decide +kernel
def pointBounds21951 : List (Nat × Nat × Nat) := [(2881120256,101224636570093,101225017637955),(2881210368,101225042882769,101225423950861)]
theorem point_links_checked21951 : (cuts21951.take 2).map (fun c => (2881093633-1+2*2^9*c.k,101224519138555+c.lower,101224900206351+c.upper)) = pointBounds21951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000060
