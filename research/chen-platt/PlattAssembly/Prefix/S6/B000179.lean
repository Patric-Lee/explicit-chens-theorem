import PlattAssemblyKernel
import PlattCertificates.Count131072.C055728
import PlattCertificates.Count131072.C055729
import PlattCertificates.Count131072.C055730
import PlattCertificates.Count131072.C055731
import PlattCertificates.Count131072.C055732
import PlattCertificates.Count131072.C055733
import PlattCertificates.Count131072.C055734
import PlattCertificates.Count131072.C055735
import PlattCertificates.Count131072.C055736
import PlattCertificates.Count131072.C055737
import PlattCertificates.Count131072.C055738
import PlattCertificates.Count131072.C055739
import PlattCertificates.Count131072.C055740
import PlattCertificates.Count131072.C055741
import PlattCertificates.Count131072.C055742
import PlattCertificates.Count131072.C055743
import PlattCertificates.Count131072.C055744
import PlattCertificates.Count131072.C055745
import PlattCertificates.Count131072.C055746
import PlattCertificates.Count131072.C055747
import PlattCertificates.Count131072.C055748
import PlattCertificates.Count131072.C055749
import PlattCertificates.Count131072.C055750
import PlattCertificates.Count131072.C055751
import PlattCertificates.Count131072.C055752
import PlattCertificates.Count131072.C055753
import PlattCertificates.Count131072.C055754
import PlattCertificates.Count131072.C055755
import PlattCertificates.Count131072.C055756
import PlattCertificates.Count131072.C055757
import PlattCertificates.Count131072.C055758
import PlattCertificates.Count131072.C055759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55728 : List PrefixCut := [⟨64,222187280,222187407⟩]
theorem checked55728 : checkPrefixCuts (2^48) 7308312577 10 Manual.Count131072.C055728.packed 64 cuts55728 = true := by
 decide +kernel
def cuts55729 : List PrefixCut := [⟨41,143732146,143732229⟩,
⟨64,224031935,224032064⟩]
theorem checked55729 : checkPrefixCuts (2^48) 7308443649 10 Manual.Count131072.C055729.packed 64 cuts55729 = true := by
 decide +kernel
def pointBounds55729 : List (Nat × Nat × Nat) := [(7308527616,113003768867750,113004156755051)]
theorem point_links_checked55729 : (cuts55729.take 1).map (fun c => (7308443649-1+2*2^10*c.k,113003625135604+c.lower,113004013022822+c.upper)) = pointBounds55729 := by
 decide +kernel
def cuts55730 : List PrefixCut := [⟨64,222911061,222911182⟩]
theorem checked55730 : checkPrefixCuts (2^48) 7308574721 10 Manual.Count131072.C055730.packed 64 cuts55730 = true := by
 decide +kernel
def cuts55731 : List PrefixCut := [⟨25,86613804,86613852⟩,
⟨64,223215159,223215284⟩]
theorem checked55731 : checkPrefixCuts (2^48) 7308705793 10 Manual.Count131072.C055731.packed 64 cuts55731 = true := by
 decide +kernel
def pointBounds55731 : List (Nat × Nat × Nat) := [(7308756992,113004158692404,113004546579920)]
theorem point_links_checked55731 : (cuts55731.take 1).map (fun c => (7308705793-1+2*2^10*c.k,113004072078600+c.lower,113004459966068+c.upper)) = pointBounds55731 := by
 decide +kernel
def cuts55732 : List PrefixCut := [⟨64,223711796,223711923⟩]
theorem checked55732 : checkPrefixCuts (2^48) 7308836865 10 Manual.Count131072.C055732.packed 64 cuts55732 = true := by
 decide +kernel
def cuts55733 : List PrefixCut := [⟨9,32041023,32041042⟩,
⟨64,224555032,224555158⟩]
theorem checked55733 : checkPrefixCuts (2^48) 7308967937 10 Manual.Count131072.C055733.packed 64 cuts55733 = true := by
 decide +kernel
def pointBounds55733 : List (Nat × Nat × Nat) := [(7308986368,113004551046578,113004938934317)]
theorem point_links_checked55733 : (cuts55733.take 1).map (fun c => (7308967937-1+2*2^10*c.k,113004519005555+c.lower,113004906893275+c.upper)) = pointBounds55733 := by
 decide +kernel
def cuts55734 : List PrefixCut := [⟨57,198518527,198518637⟩,
⟨64,223164641,223164765⟩]
theorem checked55734 : checkPrefixCuts (2^48) 7309099009 10 Manual.Count131072.C055734.packed 64 cuts55734 = true := by
 decide +kernel
def pointBounds55734 : List (Nat × Nat × Nat) := [(7309215744,113004942079114,113005329967070)]
theorem point_links_checked55734 : (cuts55734.take 1).map (fun c => (7309099009-1+2*2^10*c.k,113004743560587+c.lower,113005131448433+c.upper)) = pointBounds55734 := by
 decide +kernel
def cuts55735 : List PrefixCut := [⟨64,221774294,221774420⟩]
theorem checked55735 : checkPrefixCuts (2^48) 7309230081 10 Manual.Count131072.C055735.packed 64 cuts55735 = true := by
 decide +kernel
def cuts55736 : List PrefixCut := [⟨41,141134025,141134105⟩,
⟨64,220653581,220653705⟩]
theorem checked55736 : checkPrefixCuts (2^48) 7309361153 10 Manual.Count131072.C055736.packed 64 cuts55736 = true := by
 decide +kernel
def pointBounds55736 : List (Nat × Nat × Nat) := [(7309445120,113005329633547,113005717521723)]
theorem point_links_checked55736 : (cuts55736.take 1).map (fun c => (7309361153-1+2*2^10*c.k,113005188499522+c.lower,113005576387618+c.upper)) = pointBounds55736 := by
 decide +kernel
def cuts55737 : List PrefixCut := [⟨64,219494386,219494511⟩]
theorem checked55737 : checkPrefixCuts (2^48) 7309492225 10 Manual.Count131072.C055737.packed 64 cuts55737 = true := by
 decide +kernel
def cuts55738 : List PrefixCut := [⟨25,86756965,86757014⟩,
⟨64,220260596,220260721⟩]
theorem checked55738 : checkPrefixCuts (2^48) 7309623297 10 Manual.Count131072.C055738.packed 64 cuts55738 = true := by
 decide +kernel
def pointBounds55738 : List (Nat × Nat × Nat) := [(7309674496,113005715404454,113006103292848)]
theorem point_links_checked55738 : (cuts55738.take 1).map (fun c => (7309623297-1+2*2^10*c.k,113005628647489+c.lower,113006016535834+c.upper)) = pointBounds55738 := by
 decide +kernel
def cuts55739 : List PrefixCut := [⟨64,222181962,222182088⟩]
theorem checked55739 : checkPrefixCuts (2^48) 7309754369 10 Manual.Count131072.C055739.packed 64 cuts55739 = true := by
 decide +kernel
def cuts55740 : List PrefixCut := [⟨9,31613437,31613454⟩,
⟨64,223602706,223602833⟩]
theorem checked55740 : checkPrefixCuts (2^48) 7309885441 10 Manual.Count131072.C055740.packed 64 cuts55740 = true := by
 decide +kernel
def pointBounds55740 : List (Nat × Nat × Nat) := [(7309903872,113006102703484,113006490592097)]
theorem point_links_checked55740 : (cuts55740.take 1).map (fun c => (7309885441-1+2*2^10*c.k,113006071090047+c.lower,113006458978643+c.upper)) = pointBounds55740 := by
 decide +kernel
def cuts55741 : List PrefixCut := [⟨57,197530979,197531091⟩,
⟨64,221134371,221134496⟩]
theorem checked55741 : checkPrefixCuts (2^48) 7310016513 10 Manual.Count131072.C055741.packed 64 cuts55741 = true := by
 decide +kernel
def pointBounds55741 : List (Nat × Nat × Nat) := [(7310133248,113006492223732,113006880112567)]
theorem point_links_checked55741 : (cuts55741.take 1).map (fun c => (7310016513-1+2*2^10*c.k,113006294692753+c.lower,113006682581476+c.upper)) = pointBounds55741 := by
 decide +kernel
def cuts55742 : List PrefixCut := [⟨64,220206294,220206419⟩]
theorem checked55742 : checkPrefixCuts (2^48) 7310147585 10 Manual.Count131072.C055742.packed 64 cuts55742 = true := by
 decide +kernel
def cuts55743 : List PrefixCut := [⟨41,141693857,141693941⟩,
⟨64,221280431,221280562⟩]
theorem checked55743 : checkPrefixCuts (2^48) 7310278657 10 Manual.Count131072.C055743.packed 64 cuts55743 = true := by
 decide +kernel
def pointBounds55743 : List (Nat × Nat × Nat) := [(7310362624,113006877727275,113007265616332)]
theorem point_links_checked55743 : (cuts55743.take 1).map (fun c => (7310278657-1+2*2^10*c.k,113006736033418+c.lower,113007123922391+c.upper)) = pointBounds55743 := by
 decide +kernel
def cuts55744 : List PrefixCut := [⟨64,224125704,224125834⟩]
theorem checked55744 : checkPrefixCuts (2^48) 7310409729 10 Manual.Count131072.C055744.packed 64 cuts55744 = true := by
 decide +kernel
def cuts55745 : List PrefixCut := [⟨25,86977087,86977137⟩,
⟨64,220579474,220579601⟩]
theorem checked55745 : checkPrefixCuts (2^48) 7310540801 10 Manual.Count131072.C055745.packed 64 cuts55745 = true := by
 decide +kernel
def pointBounds55745 : List (Nat × Nat × Nat) := [(7310592000,113007268416640,113007656305924)]
theorem point_links_checked55745 : (cuts55745.take 1).map (fun c => (7310540801-1+2*2^10*c.k,113007181439553+c.lower,113007569328787+c.upper)) = pointBounds55745 := by
 decide +kernel
def cuts55746 : List PrefixCut := [⟨64,223270649,223270774⟩]
theorem checked55746 : checkPrefixCuts (2^48) 7310671873 10 Manual.Count131072.C055746.packed 64 cuts55746 = true := by
 decide +kernel
def cuts55747 : List PrefixCut := [⟨9,32648999,32649018⟩,
⟨64,223459127,223459253⟩]
theorem checked55747 : checkPrefixCuts (2^48) 7310802945 10 Manual.Count131072.C055747.packed 64 cuts55747 = true := by
 decide +kernel
def pointBounds55747 : List (Nat × Nat × Nat) := [(7310821376,113007657938675,113008045828180)]
theorem point_links_checked55747 : (cuts55747.take 1).map (fun c => (7310802945-1+2*2^10*c.k,113007625289676+c.lower,113008013179162+c.upper)) = pointBounds55747 := by
 decide +kernel
def cuts55748 : List PrefixCut := [⟨57,200239698,200239813⟩,
⟨64,225072124,225072253⟩]
theorem checked55748 : checkPrefixCuts (2^48) 7310934017 10 Manual.Count131072.C055748.packed 64 cuts55748 = true := by
 decide +kernel
def pointBounds55748 : List (Nat × Nat × Nat) := [(7311050752,113008048988501,113008436878228)]
theorem point_links_checked55748 : (cuts55748.take 1).map (fun c => (7310934017-1+2*2^10*c.k,113007848748803+c.lower,113008236638415+c.upper)) = pointBounds55748 := by
 decide +kernel
def cuts55749 : List PrefixCut := [⟨64,220024662,220024789⟩]
theorem checked55749 : checkPrefixCuts (2^48) 7311065089 10 Manual.Count131072.C055749.packed 64 cuts55749 = true := by
 decide +kernel
def cuts55750 : List PrefixCut := [⟨41,141522084,141522165⟩,
⟨64,220559693,220559815⟩]
theorem checked55750 : checkPrefixCuts (2^48) 7311196161 10 Manual.Count131072.C055750.packed 64 cuts55750 = true := by
 decide +kernel
def pointBounds55750 : List (Nat × Nat × Nat) := [(7311280128,113008435367673,113008823257622)]
theorem point_links_checked55750 : (cuts55750.take 1).map (fun c => (7311196161-1+2*2^10*c.k,113008293845589+c.lower,113008681735457+c.upper)) = pointBounds55750 := by
 decide +kernel
def cuts55751 : List PrefixCut := [⟨64,219901283,219901407⟩]
theorem checked55751 : checkPrefixCuts (2^48) 7311327233 10 Manual.Count131072.C055751.packed 64 cuts55751 = true := by
 decide +kernel
def cuts55752 : List PrefixCut := [⟨25,86311717,86311767⟩,
⟨64,221475724,221475852⟩]
theorem checked55752 : checkPrefixCuts (2^48) 7311458305 10 Manual.Count131072.C055752.packed 64 cuts55752 = true := by
 decide +kernel
def pointBounds55752 : List (Nat × Nat × Nat) := [(7311509504,113008820618282,113009208508446)]
theorem point_links_checked55752 : (cuts55752.take 1).map (fun c => (7311458305-1+2*2^10*c.k,113008734306565+c.lower,113009122196679+c.upper)) = pointBounds55752 := by
 decide +kernel
def cuts55753 : List PrefixCut := [⟨64,224705480,224705605⟩]
theorem checked55753 : checkPrefixCuts (2^48) 7311589377 10 Manual.Count131072.C055753.packed 64 cuts55753 = true := by
 decide +kernel
def cuts55754 : List PrefixCut := [⟨9,30874070,30874089⟩,
⟨64,221737247,221737374⟩]
theorem checked55754 : checkPrefixCuts (2^48) 7311720449 10 Manual.Count131072.C055754.packed 64 cuts55754 = true := by
 decide +kernel
def pointBounds55754 : List (Nat × Nat × Nat) := [(7311738880,113009211361839,113009599252225)]
theorem point_links_checked55754 : (cuts55754.take 1).map (fun c => (7311720449-1+2*2^10*c.k,113009180487769+c.lower,113009568378136+c.upper)) = pointBounds55754 := by
 decide +kernel
def cuts55755 : List PrefixCut := [⟨57,195518140,195518249⟩,
⟨64,219423570,219423693⟩]
theorem checked55755 : checkPrefixCuts (2^48) 7311851521 10 Manual.Count131072.C055755.packed 64 cuts55755 = true := by
 decide +kernel
def pointBounds55755 : List (Nat × Nat × Nat) := [(7311968256,113009597743156,113009985633759)]
theorem point_links_checked55755 : (cuts55755.take 1).map (fun c => (7311851521-1+2*2^10*c.k,113009402225016+c.lower,113009790115510+c.upper)) = pointBounds55755 := by
 decide +kernel
def cuts55756 : List PrefixCut := [⟨64,224115985,224116109⟩]
theorem checked55756 : checkPrefixCuts (2^48) 7311982593 10 Manual.Count131072.C055756.packed 64 cuts55756 = true := by
 decide +kernel
def cuts55757 : List PrefixCut := [⟨41,141157893,141157972⟩,
⟨64,222764674,222764797⟩]
theorem checked55757 : checkPrefixCuts (2^48) 7312113665 10 Manual.Count131072.C055757.packed 64 cuts55757 = true := by
 decide +kernel
def pointBounds55757 : List (Nat × Nat × Nat) := [(7312197632,113009986922464,113010374813284)]
theorem point_links_checked55757 : (cuts55757.take 1).map (fun c => (7312113665-1+2*2^10*c.k,113009845764571+c.lower,113010233655312+c.upper)) = pointBounds55757 := by
 decide +kernel
def cuts55758 : List PrefixCut := [⟨64,221413402,221413528⟩]
theorem checked55758 : checkPrefixCuts (2^48) 7312244737 10 Manual.Count131072.C055758.packed 64 cuts55758 = true := by
 decide +kernel
def cuts55759 : List PrefixCut := [⟨25,85569518,85569568⟩,
⟨64,218291549,218291675⟩]
theorem checked55759 : checkPrefixCuts (2^48) 7312375809 10 Manual.Count131072.C055759.packed 64 cuts55759 = true := by
 decide +kernel
def pointBounds55759 : List (Nat × Nat × Nat) := [(7312427008,113010375512165,113010763403205)]
theorem point_links_checked55759 : (cuts55759.take 1).map (fun c => (7312375809-1+2*2^10*c.k,113010289942647+c.lower,113010677833637+c.upper)) = pointBounds55759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000179
