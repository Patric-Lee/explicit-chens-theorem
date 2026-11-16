import PlattAssemblyKernel
import PlattCertificates.Count131072.C024640
import PlattCertificates.Count131072.C024641
import PlattCertificates.Count131072.C024642
import PlattCertificates.Count131072.C024643
import PlattCertificates.Count131072.C024644
import PlattCertificates.Count131072.C024645
import PlattCertificates.Count131072.C024646
import PlattCertificates.Count131072.C024647
import PlattCertificates.Count131072.C024648
import PlattCertificates.Count131072.C024649
import PlattCertificates.Count131072.C024650
import PlattCertificates.Count131072.C024651
import PlattCertificates.Count131072.C024652
import PlattCertificates.Count131072.C024653
import PlattCertificates.Count131072.C024654
import PlattCertificates.Count131072.C024655
import PlattCertificates.Count131072.C024656
import PlattCertificates.Count131072.C024657
import PlattCertificates.Count131072.C024658
import PlattCertificates.Count131072.C024659
import PlattCertificates.Count131072.C024660
import PlattCertificates.Count131072.C024661
import PlattCertificates.Count131072.C024662
import PlattCertificates.Count131072.C024663
import PlattCertificates.Count131072.C024664
import PlattCertificates.Count131072.C024665
import PlattCertificates.Count131072.C024666
import PlattCertificates.Count131072.C024667
import PlattCertificates.Count131072.C024668
import PlattCertificates.Count131072.C024669
import PlattCertificates.Count131072.C024670
import PlattCertificates.Count131072.C024671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24640 : List PrefixCut := [⟨7,29422314,29422330⟩,
⟨106,433232453,433232690⟩,
⟨128,522366675,522366964⟩]
theorem checked24640 : checkPrefixCuts (2^48) 3233546241 9 Manual.Count131072.C024640.packed 128 cuts24640 = true := by
 decide +kernel
def pointBounds24640 : List (Nat × Nat × Nat) := [(3233553408,102711896027493,102712277939331),(3233654784,102712299837632,102712681749691)]
theorem point_links_checked24640 : (cuts24640.take 2).map (fun c => (3233546241-1+2*2^9*c.k,102711866605179+c.lower,102712248517001+c.upper)) = pointBounds24640 := by
 decide +kernel
def cuts24641 : List PrefixCut := [⟨77,308657208,308657386⟩,
⟨128,518080273,518080569⟩]
theorem checked24641 : checkPrefixCuts (2^48) 3233677313 9 Manual.Count131072.C024641.packed 128 cuts24641 = true := by
 decide +kernel
def pointBounds24641 : List (Nat × Nat × Nat) := [(3233756160,102712697629062,102713079541351)]
theorem point_links_checked24641 : (cuts24641.take 1).map (fun c => (3233677313-1+2*2^9*c.k,102712388971854+c.lower,102712770883965+c.upper)) = pointBounds24641 := by
 decide +kernel
def cuts24642 : List PrefixCut := [⟨48,199671258,199671368⟩,
⟨128,524935524,524935818⟩]
theorem checked24642 : checkPrefixCuts (2^48) 3233808385 9 Manual.Count131072.C024642.packed 128 cuts24642 = true := by
 decide +kernel
def pointBounds24642 : List (Nat × Nat × Nat) := [(3233857536,102713106723385,102713488635902)]
theorem point_links_checked24642 : (cuts24642.take 1).map (fun c => (3233808385-1+2*2^9*c.k,102712907052127+c.lower,102713288964534+c.upper)) = pointBounds24642 := by
 decide +kernel
def cuts24643 : List PrefixCut := [⟨19,78333756,78333801⟩,
⟨118,482354385,482354657⟩,
⟨128,524827165,524827461⟩]
theorem checked24643 : checkPrefixCuts (2^48) 3233939457 9 Manual.Count131072.C024643.packed 128 cuts24643 = true := by
 decide +kernel
def pointBounds24643 : List (Nat × Nat × Nat) := [(3233958912,102713510321407,102713892234153),(3234060288,102713914342036,102714296255009)]
theorem point_links_checked24643 : (cuts24643.take 2).map (fun c => (3233939457-1+2*2^9*c.k,102713431987651+c.lower,102713813900352+c.upper)) = pointBounds24643 := by
 decide +kernel
def cuts24644 : List PrefixCut := [⟨89,360577814,360578018⟩,
⟨128,517669250,517669543⟩]
theorem checked24644 : checkPrefixCuts (2^48) 3234070529 9 Manual.Count131072.C024644.packed 128 cuts24644 = true := by
 decide +kernel
def pointBounds24644 : List (Nat × Nat × Nat) := [(3234161664,102714317392630,102714699305831)]
theorem point_links_checked24644 : (cuts24644.take 1).map (fun c => (3234070529-1+2*2^9*c.k,102713956814816+c.lower,102714338727813+c.upper)) = pointBounds24644 := by
 decide +kernel
def cuts24645 : List PrefixCut := [⟨60,246468676,246468811⟩,
⟨128,521303495,521303783⟩]
theorem checked24645 : checkPrefixCuts (2^48) 3234201601 9 Manual.Count131072.C024645.packed 128 cuts24645 = true := by
 decide +kernel
def pointBounds24645 : List (Nat × Nat × Nat) := [(3234263040,102714720952742,102715102866167)]
theorem point_links_checked24645 : (cuts24645.take 1).map (fun c => (3234201601-1+2*2^9*c.k,102714474484066+c.lower,102714856397356+c.upper)) = pointBounds24645 := by
 decide +kernel
def cuts24646 : List PrefixCut := [⟨31,127668269,127668340⟩,
⟨128,514059258,514059545⟩]
theorem checked24646 : checkPrefixCuts (2^48) 3234332673 9 Manual.Count131072.C024646.packed 128 cuts24646 = true := by
 decide +kernel
def pointBounds24646 : List (Nat × Nat × Nat) := [(3234364416,102715123455830,102715505369479)]
theorem point_links_checked24646 : (cuts24646.take 1).map (fun c => (3234332673-1+2*2^9*c.k,102714995787561+c.lower,102715377701139+c.upper)) = pointBounds24646 := by
 decide +kernel
def cuts24647 : List PrefixCut := [⟨2,9224507,9224511⟩,
⟨101,414400120,414400358⟩,
⟨128,521000242,521000541⟩]
theorem checked24647 : checkPrefixCuts (2^48) 3234463745 9 Manual.Count131072.C024647.packed 128 cuts24647 = true := by
 decide +kernel
def pointBounds24647 : List (Nat × Nat × Nat) := [(3234465792,102715519071326,102715900985195),(3234567168,102715924246939,102716306161042)]
theorem point_links_checked24647 : (cuts24647.take 2).map (fun c => (3234463745-1+2*2^9*c.k,102715509846819+c.lower,102715891760684+c.upper)) = pointBounds24647 := by
 decide +kernel
def cuts24648 : List PrefixCut := [⟨72,296213222,296213389⟩,
⟨128,530464047,530464346⟩]
theorem checked24648 : checkPrefixCuts (2^48) 3234594817 9 Manual.Count131072.C024648.packed 128 cuts24648 = true := by
 decide +kernel
def pointBounds24648 : List (Nat × Nat × Nat) := [(3234668544,102716327060283,102716708974614)]
theorem point_links_checked24648 : (cuts24648.take 1).map (fun c => (3234594817-1+2*2^9*c.k,102716030847061+c.lower,102716412761225+c.upper)) = pointBounds24648 := by
 decide +kernel
def cuts24649 : List PrefixCut := [⟨43,171508585,171508681⟩,
⟨128,518086414,518086709⟩]
theorem checked24649 : checkPrefixCuts (2^48) 3234725889 9 Manual.Count131072.C024649.packed 128 cuts24649 = true := by
 decide +kernel
def pointBounds24649 : List (Nat × Nat × Nat) := [(3234769920,102716732819693,102717114734252)]
theorem point_links_checked24649 : (cuts24649.take 1).map (fun c => (3234725889-1+2*2^9*c.k,102716561311108+c.lower,102716943225571+c.upper)) = pointBounds24649 := by
 decide +kernel
def cuts24650 : List PrefixCut := [⟨14,55166171,55166203⟩,
⟨113,467860990,467861249⟩,
⟨128,527984740,527985033⟩]
theorem checked24650 : checkPrefixCuts (2^48) 3234856961 9 Manual.Count131072.C024650.packed 128 cuts24650 = true := by
 decide +kernel
def pointBounds24650 : List (Nat × Nat × Nat) := [(3234871296,102717134563693,102717516478483),(3234972672,102717547258512,102717929173529)]
theorem point_links_checked24650 : (cuts24650.take 2).map (fun c => (3234856961-1+2*2^9*c.k,102717079397522+c.lower,102717461312280+c.upper)) = pointBounds24650 := by
 decide +kernel
def cuts24651 : List PrefixCut := [⟨84,342291085,342291274⟩,
⟨128,526484159,526484449⟩]
theorem checked24651 : checkPrefixCuts (2^48) 3234988033 9 Manual.Count131072.C024651.packed 128 cuts24651 = true := by
 decide +kernel
def pointBounds24651 : List (Nat × Nat × Nat) := [(3235074048,102717949673347,102718331588587)]
theorem point_links_checked24651 : (cuts24651.take 1).map (fun c => (3234988033-1+2*2^9*c.k,102717607382262+c.lower,102717989297313+c.upper)) = pointBounds24651 := by
 decide +kernel
def cuts24652 : List PrefixCut := [⟨55,231956081,231956209⟩,
⟨128,527419992,527420288⟩]
theorem checked24652 : checkPrefixCuts (2^48) 3235119105 9 Manual.Count131072.C024652.packed 128 cuts24652 = true := by
 decide +kernel
def pointBounds24652 : List (Nat × Nat × Nat) := [(3235175424,102718365822502,102718747737971)]
theorem point_links_checked24652 : (cuts24652.take 1).map (fun c => (3235119105-1+2*2^9*c.k,102718133866421+c.lower,102718515781762+c.upper)) = pointBounds24652 := by
 decide +kernel
def cuts24653 : List PrefixCut := [⟨26,109274707,109274769⟩,
⟨125,511651712,511652008⟩,
⟨128,523744577,523744881⟩]
theorem checked24653 : checkPrefixCuts (2^48) 3235250177 9 Manual.Count131072.C024653.packed 128 cuts24653 = true := by
 decide +kernel
def pointBounds24653 : List (Nat × Nat × Nat) := [(3235276800,102718770561120,102719152476819),(3235378176,102719172938125,102719554854058)]
theorem point_links_checked24653 : (cuts24653.take 2).map (fun c => (3235250177-1+2*2^9*c.k,102718661286413+c.lower,102719043202050+c.upper)) = pointBounds24653 := by
 decide +kernel
def cuts24654 : List PrefixCut := [⟨96,394360401,394360613⟩,
⟨128,521287444,521287726⟩]
theorem checked24654 : checkPrefixCuts (2^48) 3235381249 9 Manual.Count131072.C024654.packed 128 cuts24654 = true := by
 decide +kernel
def pointBounds24654 : List (Nat × Nat × Nat) := [(3235479552,102719579391391,102719961307544)]
theorem point_links_checked24654 : (cuts24654.take 1).map (fun c => (3235381249-1+2*2^9*c.k,102719185030990+c.lower,102719566946931+c.upper)) = pointBounds24654 := by
 decide +kernel
def cuts24655 : List PrefixCut := [⟨67,272205898,272206055⟩,
⟨128,518047486,518047781⟩]
theorem checked24655 : checkPrefixCuts (2^48) 3235512321 9 Manual.Count131072.C024655.packed 128 cuts24655 = true := by
 decide +kernel
def pointBounds24655 : List (Nat × Nat × Nat) := [(3235580928,102719978524332,102720360440712)]
theorem point_links_checked24655 : (cuts24655.take 1).map (fun c => (3235512321-1+2*2^9*c.k,102719706318434+c.lower,102720088234657+c.upper)) = pointBounds24655 := by
 decide +kernel
def cuts24656 : List PrefixCut := [⟨38,156758552,156758639⟩,
⟨128,516982793,516983079⟩]
theorem checked24656 : checkPrefixCuts (2^48) 3235643393 9 Manual.Count131072.C024656.packed 128 cuts24656 = true := by
 decide +kernel
def pointBounds24656 : List (Nat × Nat × Nat) := [(3235682304,102720381124472,102720763041077)]
theorem point_links_checked24656 : (cuts24656.take 1).map (fun c => (3235643393-1+2*2^9*c.k,102720224365920+c.lower,102720606282438+c.upper)) = pointBounds24656 := by
 decide +kernel
def cuts24657 : List PrefixCut := [⟨9,36361108,36361127⟩,
⟨108,438327205,438327452⟩,
⟨128,518440546,518440839⟩]
theorem checked24657 : checkPrefixCuts (2^48) 3235774465 9 Manual.Count131072.C024657.packed 128 cuts24657 = true := by
 decide +kernel
def pointBounds24657 : List (Nat × Nat × Nat) := [(3235783680,102720777709821,102721159626644),(3235885056,102721179675918,102721561592969)]
theorem point_links_checked24657 : (cuts24657.take 2).map (fun c => (3235774465-1+2*2^9*c.k,102720741348713+c.lower,102721123265517+c.upper)) = pointBounds24657 := by
 decide +kernel
def cuts24658 : List PrefixCut := [⟨79,318708663,318708841⟩,
⟨128,518593396,518593685⟩]
theorem checked24658 : checkPrefixCuts (2^48) 3235905537 9 Manual.Count131072.C024658.packed 128 cuts24658 = true := by
 decide +kernel
def pointBounds24658 : List (Nat × Nat × Nat) := [(3235986432,102721578497922,102721960415197)]
theorem point_links_checked24658 : (cuts24658.take 1).map (fun c => (3235905537-1+2*2^9*c.k,102721259789259+c.lower,102721641706356+c.upper)) = pointBounds24658 := by
 decide +kernel
def cuts24659 : List PrefixCut := [⟨50,200838392,200838512⟩,
⟨128,518833325,518833621⟩]
theorem checked24659 : checkPrefixCuts (2^48) 3236036609 9 Manual.Count131072.C024659.packed 128 cuts24659 = true := by
 decide +kernel
def pointBounds24659 : List (Nat × Nat × Nat) := [(3236087808,102721979221047,102722361138553)]
theorem point_links_checked24659 : (cuts24659.take 1).map (fun c => (3236036609-1+2*2^9*c.k,102721778382655+c.lower,102722160300041+c.upper)) = pointBounds24659 := by
 decide +kernel
def cuts24660 : List PrefixCut := [⟨21,86281736,86281784⟩,
⟨120,491241499,491241775⟩,
⟨128,523161115,523161409⟩]
theorem checked24660 : checkPrefixCuts (2^48) 3236167681 9 Manual.Count131072.C024660.packed 128 cuts24660 = true := by
 decide +kernel
def pointBounds24660 : List (Nat × Nat × Nat) := [(3236189184,102722383497716,102722765415446),(3236290560,102722788457479,102723170375437)]
theorem point_links_checked24660 : (cuts24660.take 2).map (fun c => (3236167681-1+2*2^9*c.k,102722297215980+c.lower,102722679133662+c.upper)) = pointBounds24660 := by
 decide +kernel
def cuts24661 : List PrefixCut := [⟨91,366069660,366069872⟩,
⟨128,515921214,515921511⟩]
theorem checked24661 : checkPrefixCuts (2^48) 3236298753 9 Manual.Count131072.C024661.packed 128 cuts24661 = true := by
 decide +kernel
def pointBounds24661 : List (Nat × Nat × Nat) := [(3236391936,102723186446755,102723568364943)]
theorem point_links_checked24661 : (cuts24661.take 1).map (fun c => (3236298753-1+2*2^9*c.k,102722820377095+c.lower,102723202295071+c.upper)) = pointBounds24661 := by
 decide +kernel
def cuts24662 : List PrefixCut := [⟨62,255430745,255430891⟩,
⟨128,530945978,530946278⟩]
theorem checked24662 : checkPrefixCuts (2^48) 3236429825 9 Manual.Count131072.C024662.packed 128 cuts24662 = true := by
 decide +kernel
def pointBounds24662 : List (Nat × Nat × Nat) := [(3236493312,102723591729054,102723973647473)]
theorem point_links_checked24662 : (cuts24662.take 1).map (fun c => (3236429825-1+2*2^9*c.k,102723336298309+c.lower,102723718216582+c.upper)) = pointBounds24662 := by
 decide +kernel
def cuts24663 : List PrefixCut := [⟨33,129841464,129841540⟩,
⟨128,515357522,515357817⟩]
theorem checked24663 : checkPrefixCuts (2^48) 3236560897 9 Manual.Count131072.C024663.packed 128 cuts24663 = true := by
 decide +kernel
def pointBounds24663 : List (Nat × Nat × Nat) := [(3236594688,102723997085751,102724379004400)]
theorem point_links_checked24663 : (cuts24663.take 1).map (fun c => (3236560897-1+2*2^9*c.k,102723867244287+c.lower,102724249162860+c.upper)) = pointBounds24663 := by
 decide +kernel
def cuts24664 : List PrefixCut := [⟨4,16697032,16697041⟩,
⟨103,416201768,416202010⟩,
⟨128,518293485,518293783⟩]
theorem checked24664 : checkPrefixCuts (2^48) 3236691969 9 Manual.Count131072.C024664.packed 128 cuts24664 = true := by
 decide +kernel
def pointBounds24664 : List (Nat × Nat × Nat) := [(3236696064,102724399298841,102724781217718),(3236797440,102724798803577,102725180722687)]
theorem point_links_checked24664 : (cuts24664.take 2).map (fun c => (3236691969-1+2*2^9*c.k,102724382601809+c.lower,102724764520677+c.upper)) = pointBounds24664 := by
 decide +kernel
def cuts24665 : List PrefixCut := [⟨74,300096269,300096434⟩,
⟨128,516446422,516446709⟩]
theorem checked24665 : checkPrefixCuts (2^48) 3236823041 9 Manual.Count131072.C024665.packed 128 cuts24665 = true := by
 decide +kernel
def pointBounds24665 : List (Nat × Nat × Nat) := [(3236898816,102725200991563,102725582910894)]
theorem point_links_checked24665 : (cuts24665.take 1).map (fun c => (3236823041-1+2*2^9*c.k,102724900895294+c.lower,102725282814460+c.upper)) = pointBounds24665 := by
 decide +kernel
def cuts24666 : List PrefixCut := [⟨45,184955633,184955739⟩,
⟨128,520077655,520077955⟩]
theorem checked24666 : checkPrefixCuts (2^48) 3236954113 9 Manual.Count131072.C024666.packed 128 cuts24666 = true := by
 decide +kernel
def pointBounds24666 : List (Nat × Nat × Nat) := [(3237000192,102725602297349,102725984216908)]
theorem point_links_checked24666 : (cuts24666.take 1).map (fun c => (3236954113-1+2*2^9*c.k,102725417341716+c.lower,102725799261169+c.upper)) = pointBounds24666 := by
 decide +kernel
def cuts24667 : List PrefixCut := [⟨16,66953790,66953826⟩,
⟨115,466234614,466234873⟩,
⟨128,522230320,522230612⟩]
theorem checked24667 : checkPrefixCuts (2^48) 3237085185 9 Manual.Count131072.C024667.packed 128 cuts24667 = true := by
 decide +kernel
def pointBounds24667 : List (Nat × Nat × Nat) := [(3237101568,102726004373161,102726386292950),(3237202944,102726403653985,102726785573997)]
theorem point_links_checked24667 : (cuts24667.take 2).map (fun c => (3237085185-1+2*2^9*c.k,102725937419371+c.lower,102726319339124+c.upper)) = pointBounds24667 := by
 decide +kernel
def cuts24668 : List PrefixCut := [⟨86,354141223,354141423⟩,
⟨128,527165222,527165515⟩]
theorem checked24668 : checkPrefixCuts (2^48) 3237216257 9 Manual.Count131072.C024668.packed 128 cuts24668 = true := by
 decide +kernel
def pointBounds24668 : List (Nat × Nat × Nat) := [(3237304320,102726813790914,102727195711159)]
theorem point_links_checked24668 : (cuts24668.take 1).map (fun c => (3237216257-1+2*2^9*c.k,102726459649691+c.lower,102726841569736+c.upper)) = pointBounds24668 := by
 decide +kernel
def cuts24669 : List PrefixCut := [⟨57,231535508,231535644⟩,
⟨128,518797224,518797522⟩]
theorem checked24669 : checkPrefixCuts (2^48) 3237347329 9 Manual.Count131072.C024669.packed 128 cuts24669 = true := by
 decide +kernel
def pointBounds24669 : List (Nat × Nat × Nat) := [(3237405696,102727218350421,102727600270895)]
theorem point_links_checked24669 : (cuts24669.take 1).map (fun c => (3237347329-1+2*2^9*c.k,102726986814913+c.lower,102727368735251+c.upper)) = pointBounds24669 := by
 decide +kernel
def cuts24670 : List PrefixCut := [⟨28,115807067,115807132⟩,
⟨127,516602781,516603077⟩,
⟨128,521123616,521123914⟩]
theorem checked24670 : checkPrefixCuts (2^48) 3237478401 9 Manual.Count131072.C024670.packed 128 cuts24670 = true := by
 decide +kernel
def pointBounds24670 : List (Nat × Nat × Nat) := [(3237507072,102727621419204,102728003339905),(3237608448,102728022214918,102728404135850)]
theorem point_links_checked24670 : (cuts24670.take 2).map (fun c => (3237478401-1+2*2^9*c.k,102727505612137+c.lower,102727887532773+c.upper)) = pointBounds24670 := by
 decide +kernel
def cuts24671 : List PrefixCut := [⟨98,394175788,394176012⟩,
⟨128,515799261,515799552⟩]
theorem checked24671 : checkPrefixCuts (2^48) 3237609473 9 Manual.Count131072.C024671.packed 128 cuts24671 = true := by
 decide +kernel
def pointBounds24671 : List (Nat × Nat × Nat) := [(3237709824,102728420911541,102728802832699)]
theorem point_links_checked24671 : (cuts24671.take 1).map (fun c => (3237609473-1+2*2^9*c.k,102728026735753+c.lower,102728408656687+c.upper)) = pointBounds24671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000145
