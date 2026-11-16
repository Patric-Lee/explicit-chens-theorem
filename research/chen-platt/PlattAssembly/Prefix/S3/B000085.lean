import PlattAssemblyKernel
import PlattCertificates.Count131072.C022720
import PlattCertificates.Count131072.C022721
import PlattCertificates.Count131072.C022722
import PlattCertificates.Count131072.C022723
import PlattCertificates.Count131072.C022724
import PlattCertificates.Count131072.C022725
import PlattCertificates.Count131072.C022726
import PlattCertificates.Count131072.C022727
import PlattCertificates.Count131072.C022728
import PlattCertificates.Count131072.C022729
import PlattCertificates.Count131072.C022730
import PlattCertificates.Count131072.C022731
import PlattCertificates.Count131072.C022732
import PlattCertificates.Count131072.C022733
import PlattCertificates.Count131072.C022734
import PlattCertificates.Count131072.C022735
import PlattCertificates.Count131072.C022736
import PlattCertificates.Count131072.C022737
import PlattCertificates.Count131072.C022738
import PlattCertificates.Count131072.C022739
import PlattCertificates.Count131072.C022740
import PlattCertificates.Count131072.C022741
import PlattCertificates.Count131072.C022742
import PlattCertificates.Count131072.C022743
import PlattCertificates.Count131072.C022744
import PlattCertificates.Count131072.C022745
import PlattCertificates.Count131072.C022746
import PlattCertificates.Count131072.C022747
import PlattCertificates.Count131072.C022748
import PlattCertificates.Count131072.C022749
import PlattCertificates.Count131072.C022750
import PlattCertificates.Count131072.C022751
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000085
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22720 : List PrefixCut := [⟨80,350577689,350577893⟩,
⟨128,568999616,568999944⟩]
theorem checked22720 : checkPrefixCuts (2^48) 2981888001 9 Manual.Count131072.C022720.packed 128 cuts22720 = true := by
 decide +kernel
def pointBounds22720 : List (Nat × Nat × Nat) := [(2981969920,101668832571373,101669213893092)]
theorem point_links_checked22720 : (cuts22720.take 1).map (fun c => (2981888001-1+2*2^9*c.k,101668481993684+c.lower,101668863315199+c.upper)) = pointBounds22720 := by
 decide +kernel
def cuts22721 : List PrefixCut := [⟨44,194254620,194254732⟩,
⟨128,567464435,567464755⟩]
theorem checked22721 : checkPrefixCuts (2^48) 2982019073 9 Manual.Count131072.C022721.packed 128 cuts22721 = true := by
 decide +kernel
def pointBounds22721 : List (Nat × Nat × Nat) := [(2982064128,101669245247920,101669626569875)]
theorem point_links_checked22721 : (cuts22721.take 1).map (fun c => (2982019073-1+2*2^9*c.k,101669050993300+c.lower,101669432315143+c.upper)) = pointBounds22721 := by
 decide +kernel
def cuts22722 : List PrefixCut := [⟨8,33695953,33695973⟩,
⟨100,444647425,444647672⟩,
⟨128,570082255,570082575⟩]
theorem checked22722 : checkPrefixCuts (2^48) 2982150145 9 Manual.Count131072.C022722.packed 128 cuts22722 = true := by
 decide +kernel
def pointBounds22722 : List (Nat × Nat × Nat) := [(2982158336,101669652153688,101670033475871),(2982252544,101670063105160,101670444427570)]
theorem point_links_checked22722 : (cuts22722.take 2).map (fun c => (2982150145-1+2*2^9*c.k,101669618457735+c.lower,101669999779898+c.upper)) = pointBounds22722 := by
 decide +kernel
def cuts22723 : List PrefixCut := [⟨64,287580035,287580193⟩,
⟨128,571378601,571378911⟩]
theorem checked22723 : checkPrefixCuts (2^48) 2982281217 9 Manual.Count131072.C022723.packed 128 cuts22723 = true := by
 decide +kernel
def pointBounds22723 : List (Nat × Nat × Nat) := [(2982346752,101670476120025,101670857442666)]
theorem point_links_checked22723 : (cuts22723.take 1).map (fun c => (2982281217-1+2*2^9*c.k,101670188539990+c.lower,101670569862473+c.upper)) = pointBounds22723 := by
 decide +kernel
def cuts22724 : List PrefixCut := [⟨28,123823686,123823758⟩,
⟨120,537095646,537095947⟩,
⟨128,573052235,573052557⟩]
theorem checked22724 : checkPrefixCuts (2^48) 2982412289 9 Manual.Count131072.C022724.packed 128 cuts22724 = true := by
 decide +kernel
def pointBounds22724 : List (Nat × Nat × Nat) := [(2982440960,101670883742277,101671265065142),(2982535168,101671297014237,101671678337331)]
theorem point_links_checked22724 : (cuts22724.take 2).map (fun c => (2982412289-1+2*2^9*c.k,101670759918591+c.lower,101671141241384+c.upper)) = pointBounds22724 := by
 decide +kernel
def cuts22725 : List PrefixCut := [⟨84,372489263,372489475⟩,
⟨128,572649494,572649822⟩]
theorem checked22725 : checkPrefixCuts (2^48) 2982543361 9 Manual.Count131072.C022725.packed 128 cuts22725 = true := by
 decide +kernel
def pointBounds22725 : List (Nat × Nat × Nat) := [(2982629376,101671705460089,101672086783416)]
theorem point_links_checked22725 : (cuts22725.take 1).map (fun c => (2982543361-1+2*2^9*c.k,101671332970826+c.lower,101671714293941+c.upper)) = pointBounds22725 := by
 decide +kernel
def cuts22726 : List PrefixCut := [⟨48,213934966,213935089⟩,
⟨128,572152524,572152864⟩]
theorem checked22726 : checkPrefixCuts (2^48) 2982674433 9 Manual.Count131072.C022726.packed 128 cuts22726 = true := by
 decide +kernel
def pointBounds22726 : List (Nat × Nat × Nat) := [(2982723584,101672119555286,101672500878852)]
theorem point_links_checked22726 : (cuts22726.take 1).map (fun c => (2982674433-1+2*2^9*c.k,101671905620320+c.lower,101672286943763+c.upper)) = pointBounds22726 := by
 decide +kernel
def cuts22727 : List PrefixCut := [⟨12,50863076,50863103⟩,
⟨104,458326566,458326822⟩,
⟨128,565993685,565993998⟩]
theorem checked22727 : checkPrefixCuts (2^48) 2982805505 9 Manual.Count131072.C022727.packed 128 cuts22727 = true := by
 decide +kernel
def pointBounds22727 : List (Nat × Nat × Nat) := [(2982817792,101672528635920,101672909959730),(2982912000,101672936099410,101673317423449)]
theorem point_links_checked22727 : (cuts22727.take 2).map (fun c => (2982805505-1+2*2^9*c.k,101672477772844+c.lower,101672859096627+c.upper)) = pointBounds22727 := by
 decide +kernel
def cuts22728 : List PrefixCut := [⟨68,294310662,294310833⟩,
⟨128,561345224,561345546⟩]
theorem checked22728 : checkPrefixCuts (2^48) 2982936577 9 Manual.Count131072.C022728.packed 128 cuts22728 = true := by
 decide +kernel
def pointBounds22728 : List (Nat × Nat × Nat) := [(2983006208,101673338077191,101673719401458)]
theorem point_links_checked22728 : (cuts22728.take 1).map (fun c => (2982936577-1+2*2^9*c.k,101673043766529+c.lower,101673425090625+c.upper)) = pointBounds22728 := by
 decide +kernel
def cuts22729 : List PrefixCut := [⟨32,139648377,139648457⟩,
⟨124,546129734,546130052⟩,
⟨128,564245596,564245924⟩]
theorem checked22729 : checkPrefixCuts (2^48) 2983067649 9 Manual.Count131072.C022729.packed 128 cuts22729 = true := by
 decide +kernel
def pointBounds22729 : List (Nat × Nat × Nat) := [(2983100416,101673744760130,101674126084628),(2983194624,101674151241487,101674532566223)]
theorem point_links_checked22729 : (cuts22729.take 2).map (fun c => (2983067649-1+2*2^9*c.k,101673605111753+c.lower,101673986436171+c.upper)) = pointBounds22729 := by
 decide +kernel
def cuts22730 : List PrefixCut := [⟨88,390805826,390806044⟩,
⟨128,574127651,574127977⟩]
theorem checked22730 : checkPrefixCuts (2^48) 2983198721 9 Manual.Count131072.C022730.packed 128 cuts22730 = true := by
 decide +kernel
def pointBounds22730 : List (Nat × Nat × Nat) := [(2983288832,101674560163175,101674941488139)]
theorem point_links_checked22730 : (cuts22730.take 1).map (fun c => (2983198721-1+2*2^9*c.k,101674169357349+c.lower,101674550682095+c.upper)) = pointBounds22730 := by
 decide +kernel
def cuts22731 : List PrefixCut := [⟨52,225587010,225587142⟩,
⟨128,557780408,557780730⟩]
theorem checked22731 : checkPrefixCuts (2^48) 2983329793 9 Manual.Count131072.C022731.packed 128 cuts22731 = true := by
 decide +kernel
def pointBounds22731 : List (Nat × Nat × Nat) := [(2983383040,101674969072010,101675350397214)]
theorem point_links_checked22731 : (cuts22731.take 1).map (fun c => (2983329793-1+2*2^9*c.k,101674743485000+c.lower,101675124810072+c.upper)) = pointBounds22731 := by
 decide +kernel
def cuts22732 : List PrefixCut := [⟨16,73211590,73211631⟩,
⟨108,477754806,477755080⟩,
⟨128,563511021,563511342⟩]
theorem checked22732 : checkPrefixCuts (2^48) 2983460865 9 Manual.Count131072.C022732.packed 128 cuts22732 = true := by
 decide +kernel
def pointBounds22732 : List (Nat × Nat × Nat) := [(2983477248,101675374476998,101675755802433),(2983571456,101675779020214,101676160345882)]
theorem point_links_checked22732 : (cuts22732.take 2).map (fun c => (2983460865-1+2*2^9*c.k,101675301265408+c.lower,101675682590802+c.upper)) = pointBounds22732 := by
 decide +kernel
def cuts22733 : List PrefixCut := [⟨72,320566591,320566773⟩,
⟨128,566976702,566977024⟩]
theorem checked22733 : checkPrefixCuts (2^48) 2983591937 9 Manual.Count131072.C022733.packed 128 cuts22733 = true := by
 decide +kernel
def pointBounds22733 : List (Nat × Nat × Nat) := [(2983665664,101676185343020,101676566668917)]
theorem point_links_checked22733 : (cuts22733.take 1).map (fun c => (2983591937-1+2*2^9*c.k,101675864776429+c.lower,101676246102144+c.upper)) = pointBounds22733 := by
 decide +kernel
def cuts22734 : List PrefixCut := [⟨36,163579016,163579110⟩,
⟨128,576196635,576196961⟩]
theorem checked22734 : checkPrefixCuts (2^48) 2983723009 9 Manual.Count131072.C022734.packed 128 cuts22734 = true := by
 decide +kernel
def pointBounds22734 : List (Nat × Nat × Nat) := [(2983759872,101676595332147,101676976658278),(2983854080,101677007949766,101677389276129)]
theorem point_links_checked22734 : (cuts22734.take 2).map (fun c => (2983723009-1+2*2^9*c.k,101676431753131+c.lower,101676813079168+c.upper)) = pointBounds22734 := by
 decide +kernel
def cuts22735 : List PrefixCut := [⟨92,404680686,404680918⟩,
⟨128,569096318,569096642⟩]
theorem checked22735 : checkPrefixCuts (2^48) 2983854081 9 Manual.Count131072.C022735.packed 128 cuts22735 = true := by
 decide +kernel
def pointBounds22735 : List (Nat × Nat × Nat) := [(2983948288,101677412630452,101677793957047)]
theorem point_links_checked22735 : (cuts22735.take 1).map (fun c => (2983854081-1+2*2^9*c.k,101677007949766+c.lower,101677389276129+c.upper)) = pointBounds22735 := by
 decide +kernel
def cuts22736 : List PrefixCut := [⟨56,242987937,242988076⟩,
⟨128,562374169,562374489⟩]
theorem checked22736 : checkPrefixCuts (2^48) 2983985153 9 Manual.Count131072.C022736.packed 128 cuts22736 = true := by
 decide +kernel
def pointBounds22736 : List (Nat × Nat × Nat) := [(2984042496,101677820034021,101678201360847)]
theorem point_links_checked22736 : (cuts22736.take 1).map (fun c => (2983985153-1+2*2^9*c.k,101677577046084+c.lower,101677958372771+c.upper)) = pointBounds22736 := by
 decide +kernel
def cuts22737 : List PrefixCut := [⟨20,90645409,90645458⟩,
⟨112,498023133,498023424⟩,
⟨128,573102236,573102571⟩]
theorem checked22737 : checkPrefixCuts (2^48) 2984116225 9 Manual.Count131072.C022737.packed 128 cuts22737 = true := by
 decide +kernel
def pointBounds22737 : List (Nat × Nat × Nat) := [(2984136704,101678230065662,101678611392718),(2984230912,101678637443386,101679018770684)]
theorem point_links_checked22737 : (cuts22737.take 2).map (fun c => (2984116225-1+2*2^9*c.k,101678139420253+c.lower,101678520747260+c.upper)) = pointBounds22737 := by
 decide +kernel
def cuts22738 : List PrefixCut := [⟨76,331248337,331248526⟩,
⟨128,561570294,561570612⟩]
theorem checked22738 : checkPrefixCuts (2^48) 2984247297 9 Manual.Count131072.C022738.packed 128 cuts22738 = true := by
 decide +kernel
def pointBounds22738 : List (Nat × Nat × Nat) := [(2984325120,101679043770826,101679425098357)]
theorem point_links_checked22738 : (cuts22738.take 1).map (fun c => (2984247297-1+2*2^9*c.k,101678712522489+c.lower,101679093849831+c.upper)) = pointBounds22738 := by
 decide +kernel
def cuts22739 : List PrefixCut := [⟨40,174766526,174766627⟩,
⟨128,556829950,556830273⟩]
theorem checked22739 : checkPrefixCuts (2^48) 2984378369 9 Manual.Count131072.C022739.packed 128 cuts22739 = true := by
 decide +kernel
def pointBounds22739 : List (Nat × Nat × Nat) := [(2984419328,101679448859309,101679830187070)]
theorem point_links_checked22739 : (cuts22739.take 1).map (fun c => (2984378369-1+2*2^9*c.k,101679274092783+c.lower,101679655420443+c.upper)) = pointBounds22739 := by
 decide +kernel
def cuts22740 : List PrefixCut := [⟨4,16127332,16127341⟩,
⟨96,421473193,421473426⟩,
⟨128,565670630,565670940⟩]
theorem checked22740 : checkPrefixCuts (2^48) 2984509441 9 Manual.Count131072.C022740.packed 128 cuts22740 = true := by
 decide +kernel
def pointBounds22740 : List (Nat × Nat × Nat) := [(2984513536,101679847050065,101680228378057),(2984607744,101680252395926,101680633724142)]
theorem point_links_checked22740 : (cuts22740.take 2).map (fun c => (2984509441-1+2*2^9*c.k,101679830922733+c.lower,101680212250716+c.upper)) = pointBounds22740 := by
 decide +kernel
def cuts22741 : List PrefixCut := [⟨60,262927475,262927623⟩,
⟨128,564042586,564042912⟩]
theorem checked22741 : checkPrefixCuts (2^48) 2984640513 9 Manual.Count131072.C022741.packed 128 cuts22741 = true := by
 decide +kernel
def pointBounds22741 : List (Nat × Nat × Nat) := [(2984701952,101680659520838,101681040849279)]
theorem point_links_checked22741 : (cuts22741.take 1).map (fun c => (2984640513-1+2*2^9*c.k,101680396593363+c.lower,101680777921656+c.upper)) = pointBounds22741 := by
 decide +kernel
def cuts22742 : List PrefixCut := [⟨24,102790568,102790628⟩,
⟨116,517056599,517056891⟩,
⟨128,568544241,568544563⟩]
theorem checked22742 : checkPrefixCuts (2^48) 2984771585 9 Manual.Count131072.C022742.packed 128 cuts22742 = true := by
 decide +kernel
def pointBounds22742 : List (Nat × Nat × Nat) := [(2984796160,101681063426517,101681444755196),(2984890368,101681477692548,101681859021459)]
theorem point_links_checked22742 : (cuts22742.take 2).map (fun c => (2984771585-1+2*2^9*c.k,101680960635949+c.lower,101681341964568+c.upper)) = pointBounds22742 := by
 decide +kernel
def cuts22743 : List PrefixCut := [⟨80,352298211,352298418⟩,
⟨128,561069921,561070243⟩]
theorem checked22743 : checkPrefixCuts (2^48) 2984902657 9 Manual.Count131072.C022743.packed 128 cuts22743 = true := by
 decide +kernel
def pointBounds22743 : List (Nat × Nat × Nat) := [(2984984576,101681881478401,101682262807549)]
theorem point_links_checked22743 : (cuts22743.take 1).map (fun c => (2984902657-1+2*2^9*c.k,101681529180190+c.lower,101681910509131+c.upper)) = pointBounds22743 := by
 decide +kernel
def cuts22744 : List PrefixCut := [⟨44,196887287,196887403⟩,
⟨128,569060222,569060538⟩]
theorem checked22744 : checkPrefixCuts (2^48) 2985033729 9 Manual.Count131072.C022744.packed 128 cuts22744 = true := by
 decide +kernel
def pointBounds22744 : List (Nat × Nat × Nat) := [(2985078784,101682287137398,101682668466777)]
theorem point_links_checked22744 : (cuts22744.take 1).map (fun c => (2985033729-1+2*2^9*c.k,101682090250111+c.lower,101682471579374+c.upper)) = pointBounds22744 := by
 decide +kernel
def cuts22745 : List PrefixCut := [⟨8,33944800,33944821⟩,
⟨100,436655282,436655523⟩,
⟨128,564414922,564415237⟩]
theorem checked22745 : checkPrefixCuts (2^48) 2985164801 9 Manual.Count131072.C022745.packed 128 cuts22745 = true := by
 decide +kernel
def pointBounds22745 : List (Nat × Nat × Nat) := [(2985172992,101682693255133,101683074584733),(2985267200,101683095965615,101683477295435)]
theorem point_links_checked22745 : (cuts22745.take 2).map (fun c => (2985164801-1+2*2^9*c.k,101682659310333+c.lower,101683040639912+c.upper)) = pointBounds22745 := by
 decide +kernel
def cuts22746 : List PrefixCut := [⟨64,287006798,287006958⟩,
⟨128,572498725,572499046⟩]
theorem checked22746 : checkPrefixCuts (2^48) 2985295873 9 Manual.Count131072.C022746.packed 128 cuts22746 = true := by
 decide +kernel
def pointBounds22746 : List (Nat × Nat × Nat) := [(2985361408,101683510732053,101683892062107)]
theorem point_links_checked22746 : (cuts22746.take 1).map (fun c => (2985295873-1+2*2^9*c.k,101683223725255+c.lower,101683605055149+c.upper)) = pointBounds22746 := by
 decide +kernel
def cuts22747 : List PrefixCut := [⟨28,126998542,126998613⟩,
⟨120,533724935,533725243⟩,
⟨128,568985265,568985591⟩]
theorem checked22747 : checkPrefixCuts (2^48) 2985426945 9 Manual.Count131072.C022747.packed 128 cuts22747 = true := by
 decide +kernel
def pointBounds22747 : List (Nat × Nat × Nat) := [(2985455616,101683923222522,101684304552808),(2985549824,101684329948915,101684711279438)]
theorem point_links_checked22747 : (cuts22747.take 2).map (fun c => (2985426945-1+2*2^9*c.k,101683796223980+c.lower,101684177554195+c.upper)) = pointBounds22747 := by
 decide +kernel
def cuts22748 : List PrefixCut := [⟨84,380975229,380975444⟩,
⟨128,571222987,571223311⟩]
theorem checked22748 : checkPrefixCuts (2^48) 2985558017 9 Manual.Count131072.C022748.packed 128 cuts22748 = true := by
 decide +kernel
def pointBounds22748 : List (Nat × Nat × Nat) := [(2985644032,101684746184474,101685127515230)]
theorem point_links_checked22748 : (cuts22748.take 1).map (fun c => (2985558017-1+2*2^9*c.k,101684365209245+c.lower,101684746539786+c.upper)) = pointBounds22748 := by
 decide +kernel
def cuts22749 : List PrefixCut := [⟨48,208910977,208911095⟩,
⟨128,559602242,559602559⟩]
theorem checked22749 : checkPrefixCuts (2^48) 2985689089 9 Manual.Count131072.C022749.packed 128 cuts22749 = true := by
 decide +kernel
def pointBounds22749 : List (Nat × Nat × Nat) := [(2985738240,101685145343209,101685526674192)]
theorem point_links_checked22749 : (cuts22749.take 1).map (fun c => (2985689089-1+2*2^9*c.k,101684936432232+c.lower,101685317763097+c.upper)) = pointBounds22749 := by
 decide +kernel
def cuts22750 : List PrefixCut := [⟨12,54205452,54205483⟩,
⟨104,455978557,455978811⟩,
⟨128,562028705,562029016⟩]
theorem checked22750 : checkPrefixCuts (2^48) 2985820161 9 Manual.Count131072.C022750.packed 128 cuts22750 = true := by
 decide +kernel
def pointBounds22750 : List (Nat × Nat × Nat) := [(2985832448,101685550239926,101685931571139),(2985926656,101685952013031,101686333344467)]
theorem point_links_checked22750 : (cuts22750.take 2).map (fun c => (2985820161-1+2*2^9*c.k,101685496034474+c.lower,101685877365656+c.upper)) = pointBounds22750 := by
 decide +kernel
def cuts22751 : List PrefixCut := [⟨68,300329283,300329451⟩,
⟨128,570110662,570110983⟩]
theorem checked22751 : checkPrefixCuts (2^48) 2985951233 9 Manual.Count131072.C022751.packed 128 cuts22751 = true := by
 decide +kernel
def pointBounds22751 : List (Nat × Nat × Nat) := [(2986020864,101686358392462,101686739724123)]
theorem point_links_checked22751 : (cuts22751.take 1).map (fun c => (2985951233-1+2*2^9*c.k,101686058063179+c.lower,101686439394672+c.upper)) = pointBounds22751 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000085
