import PlattAssemblyKernel
import PlattCertificates.Count131072.C051728
import PlattCertificates.Count131072.C051729
import PlattCertificates.Count131072.C051730
import PlattCertificates.Count131072.C051731
import PlattCertificates.Count131072.C051732
import PlattCertificates.Count131072.C051733
import PlattCertificates.Count131072.C051734
import PlattCertificates.Count131072.C051735
import PlattCertificates.Count131072.C051736
import PlattCertificates.Count131072.C051737
import PlattCertificates.Count131072.C051738
import PlattCertificates.Count131072.C051739
import PlattCertificates.Count131072.C051740
import PlattCertificates.Count131072.C051741
import PlattCertificates.Count131072.C051742
import PlattCertificates.Count131072.C051743
import PlattCertificates.Count131072.C051744
import PlattCertificates.Count131072.C051745
import PlattCertificates.Count131072.C051746
import PlattCertificates.Count131072.C051747
import PlattCertificates.Count131072.C051748
import PlattCertificates.Count131072.C051749
import PlattCertificates.Count131072.C051750
import PlattCertificates.Count131072.C051751
import PlattCertificates.Count131072.C051752
import PlattCertificates.Count131072.C051753
import PlattCertificates.Count131072.C051754
import PlattCertificates.Count131072.C051755
import PlattCertificates.Count131072.C051756
import PlattCertificates.Count131072.C051757
import PlattCertificates.Count131072.C051758
import PlattCertificates.Count131072.C051759
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51728 : List PrefixCut := [⟨11,41864190,41864213⟩,
⟨64,238528556,238528689⟩]
theorem checked51728 : checkPrefixCuts (2^48) 6784024577 10 Manual.Count131072.C051728.packed 64 cuts51728 = true := by
 decide +kernel
def pointBounds51728 : List (Nat × Nat × Nat) := [(6784047104,112079460321568,112079847683922)]
theorem point_links_checked51728 : (cuts51728.take 1).map (fun c => (6784024577-1+2*2^10*c.k,112079418457378+c.lower,112079805819709+c.upper)) = pointBounds51728 := by
 decide +kernel
def cuts51729 : List PrefixCut := [⟨51,189359093,189359199⟩,
⟨64,239187767,239187901⟩]
theorem checked51729 : checkPrefixCuts (2^48) 6784155649 10 Manual.Count131072.C051729.packed 64 cuts51729 = true := by
 decide +kernel
def pointBounds51729 : List (Nat × Nat × Nat) := [(6784260096,112079846345027,112080233707597)]
theorem point_links_checked51729 : (cuts51729.take 1).map (fun c => (6784155649-1+2*2^10*c.k,112079656985934+c.lower,112080044348398+c.upper)) = pointBounds51729 := by
 decide +kernel
def cuts51730 : List PrefixCut := [⟨64,240261829,240261966⟩]
theorem checked51730 : checkPrefixCuts (2^48) 6784286721 10 Manual.Count131072.C051730.packed 64 cuts51730 = true := by
 decide +kernel
def cuts51731 : List PrefixCut := [⟨27,99364400,99364458⟩,
⟨64,236274352,236274490⟩]
theorem checked51731 : checkPrefixCuts (2^48) 6784417793 10 Manual.Count131072.C051731.packed 64 cuts51731 = true := by
 decide +kernel
def pointBounds51731 : List (Nat × Nat × Nat) := [(6784473088,112080235799930,112080623162723)]
theorem point_links_checked51731 : (cuts51731.take 1).map (fun c => (6784417793-1+2*2^10*c.k,112080136435530+c.lower,112080523798265+c.upper)) = pointBounds51731 := by
 decide +kernel
def cuts51732 : List PrefixCut := [⟨64,236601726,236601865⟩]
theorem checked51732 : checkPrefixCuts (2^48) 6784548865 10 Manual.Count131072.C051732.packed 64 cuts51732 = true := by
 decide +kernel
def cuts51733 : List PrefixCut := [⟨3,12446046,12446052⟩,
⟨64,241326597,241326731⟩]
theorem checked51733 : checkPrefixCuts (2^48) 6784679937 10 Manual.Count131072.C051733.packed 64 cuts51733 = true := by
 decide +kernel
def pointBounds51733 : List (Nat × Nat × Nat) := [(6784686080,112080621757654,112081009120672)]
theorem point_links_checked51733 : (cuts51733.take 1).map (fun c => (6784679937-1+2*2^10*c.k,112080609311608+c.lower,112080996674620+c.upper)) = pointBounds51733 := by
 decide +kernel
def cuts51734 : List PrefixCut := [⟨43,160425435,160425528⟩,
⟨64,240492187,240492328⟩]
theorem checked51734 : checkPrefixCuts (2^48) 6784811009 10 Manual.Count131072.C051734.packed 64 cuts51734 = true := by
 decide +kernel
def pointBounds51734 : List (Nat × Nat × Nat) := [(6784899072,112081011063640,112081398426879)]
theorem point_links_checked51734 : (cuts51734.take 1).map (fun c => (6784811009-1+2*2^10*c.k,112080850638205+c.lower,112081238001351+c.upper)) = pointBounds51734 := by
 decide +kernel
def cuts51735 : List PrefixCut := [⟨64,242437347,242437487⟩]
theorem checked51735 : checkPrefixCuts (2^48) 6784942081 10 Manual.Count131072.C051735.packed 64 cuts51735 = true := by
 decide +kernel
def cuts51736 : List PrefixCut := [⟨19,69403255,69403295⟩,
⟨64,236044131,236044267⟩]
theorem checked51736 : checkPrefixCuts (2^48) 6785073153 10 Manual.Count131072.C051736.packed 64 cuts51736 = true := by
 decide +kernel
def pointBounds51736 : List (Nat × Nat × Nat) := [(6785112064,112081402970994,112081790334461)]
theorem point_links_checked51736 : (cuts51736.take 1).map (fun c => (6785073153-1+2*2^10*c.k,112081333567739+c.lower,112081720931166+c.upper)) = pointBounds51736 := by
 decide +kernel
def cuts51737 : List PrefixCut := [⟨59,219612365,219612490⟩,
⟨64,239358206,239358343⟩]
theorem checked51737 : checkPrefixCuts (2^48) 6785204225 10 Manual.Count131072.C051737.packed 64 cuts51737 = true := by
 decide +kernel
def pointBounds51737 : List (Nat × Nat × Nat) := [(6785325056,112081789224235,112082176587923)]
theorem point_links_checked51737 : (cuts51737.take 1).map (fun c => (6785204225-1+2*2^10*c.k,112081569611870+c.lower,112081956975433+c.upper)) = pointBounds51737 := by
 decide +kernel
def cuts51738 : List PrefixCut := [⟨64,240556594,240556730⟩]
theorem checked51738 : checkPrefixCuts (2^48) 6785335297 10 Manual.Count131072.C051738.packed 64 cuts51738 = true := by
 decide +kernel
def cuts51739 : List PrefixCut := [⟨35,129298789,129298862⟩,
⟨64,238063036,238063173⟩]
theorem checked51739 : checkPrefixCuts (2^48) 6785466369 10 Manual.Count131072.C051739.packed 64 cuts51739 = true := by
 decide +kernel
def pointBounds51739 : List (Nat × Nat × Nat) := [(6785538048,112082178825459,112082566189368)]
theorem point_links_checked51739 : (cuts51739.take 1).map (fun c => (6785466369-1+2*2^10*c.k,112082049526670+c.lower,112082436890506+c.upper)) = pointBounds51739 := by
 decide +kernel
def cuts51740 : List PrefixCut := [⟨64,243285031,243285172⟩]
theorem checked51740 : checkPrefixCuts (2^48) 6785597441 10 Manual.Count131072.C051740.packed 64 cuts51740 = true := by
 decide +kernel
def cuts51741 : List PrefixCut := [⟨11,41397395,41397418⟩,
⟨64,238676061,238676200⟩]
theorem checked51741 : checkPrefixCuts (2^48) 6785728513 10 Manual.Count131072.C051741.packed 64 cuts51741 = true := by
 decide +kernel
def pointBounds51741 : List (Nat × Nat × Nat) := [(6785751040,112082572272132,112082959636269)]
theorem point_links_checked51741 : (cuts51741.take 1).map (fun c => (6785728513-1+2*2^10*c.k,112082530874737+c.lower,112082918238851+c.upper)) = pointBounds51741 := by
 decide +kernel
def cuts51742 : List PrefixCut := [⟨51,190348517,190348628⟩,
⟨64,238920315,238920454⟩]
theorem checked51742 : checkPrefixCuts (2^48) 6785859585 10 Manual.Count131072.C051742.packed 64 cuts51742 = true := by
 decide +kernel
def pointBounds51742 : List (Nat × Nat × Nat) := [(6785964032,112082959899315,112083347263679)]
theorem point_links_checked51742 : (cuts51742.take 1).map (fun c => (6785859585-1+2*2^10*c.k,112082769550798+c.lower,112083156915051+c.upper)) = pointBounds51742 := by
 decide +kernel
def cuts51743 : List PrefixCut := [⟨64,238666875,238667015⟩]
theorem checked51743 : checkPrefixCuts (2^48) 6785990657 10 Manual.Count131072.C051743.packed 64 cuts51743 = true := by
 decide +kernel
def cuts51744 : List PrefixCut := [⟨27,104731579,104731637⟩,
⟨64,245879339,245879477⟩]
theorem checked51744 : checkPrefixCuts (2^48) 6786121729 10 Manual.Count131072.C051744.packed 64 cuts51744 = true := by
 decide +kernel
def pointBounds51744 : List (Nat × Nat × Nat) := [(6786177024,112083351869567,112083739234157)]
theorem point_links_checked51744 : (cuts51744.take 1).map (fun c => (6786121729-1+2*2^10*c.k,112083247137988+c.lower,112083634502520+c.upper)) = pointBounds51744 := by
 decide +kernel
def cuts51745 : List PrefixCut := [⟨64,240275208,240275345⟩]
theorem checked51745 : checkPrefixCuts (2^48) 6786252801 10 Manual.Count131072.C051745.packed 64 cuts51745 = true := by
 decide +kernel
def cuts51746 : List PrefixCut := [⟨3,12194062,12194069⟩,
⟨64,241017158,241017297⟩]
theorem checked51746 : checkPrefixCuts (2^48) 6786383873 10 Manual.Count131072.C051746.packed 64 cuts51746 = true := by
 decide +kernel
def pointBounds51746 : List (Nat × Nat × Nat) := [(6786390016,112083745486597,112084132851411)]
theorem point_links_checked51746 : (cuts51746.take 1).map (fun c => (6786383873-1+2*2^10*c.k,112083733292535+c.lower,112084120657342+c.upper)) = pointBounds51746 := by
 decide +kernel
def cuts51747 : List PrefixCut := [⟨43,159928951,159929044⟩,
⟨64,239809701,239809843⟩]
theorem checked51747 : checkPrefixCuts (2^48) 6786514945 10 Manual.Count131072.C051747.packed 64 cuts51747 = true := by
 decide +kernel
def pointBounds51747 : List (Nat × Nat × Nat) := [(6786603008,112084134238644,112084521603683)]
theorem point_links_checked51747 : (cuts51747.take 1).map (fun c => (6786514945-1+2*2^10*c.k,112083974309693+c.lower,112084361674639+c.upper)) = pointBounds51747 := by
 decide +kernel
def cuts51748 : List PrefixCut := [⟨64,239431789,239431925⟩]
theorem checked51748 : checkPrefixCuts (2^48) 6786646017 10 Manual.Count131072.C051748.packed 64 cuts51748 = true := by
 decide +kernel
def cuts51749 : List PrefixCut := [⟨19,72869635,72869676⟩,
⟨64,241169093,241169233⟩]
theorem checked51749 : checkPrefixCuts (2^48) 6786777089 10 Manual.Count131072.C051749.packed 64 cuts51749 = true := by
 decide +kernel
def pointBounds51749 : List (Nat × Nat × Nat) := [(6786816000,112084526420818,112084913786083)]
theorem point_links_checked51749 : (cuts51749.take 1).map (fun c => (6786777089-1+2*2^10*c.k,112084453551183+c.lower,112084840916407+c.upper)) = pointBounds51749 := by
 decide +kernel
def cuts51750 : List PrefixCut := [⟨59,220262275,220262403⟩,
⟨64,238095426,238095564⟩]
theorem checked51750 : checkPrefixCuts (2^48) 6786908161 10 Manual.Count131072.C051750.packed 64 cuts51750 = true := by
 decide +kernel
def pointBounds51750 : List (Nat × Nat × Nat) := [(6787028992,112084914982551,112085302348043)]
theorem point_links_checked51750 : (cuts51750.take 1).map (fun c => (6786908161-1+2*2^10*c.k,112084694720276+c.lower,112085082085640+c.upper)) = pointBounds51750 := by
 decide +kernel
def cuts51751 : List PrefixCut := [⟨64,240040007,240040144⟩]
theorem checked51751 : checkPrefixCuts (2^48) 6787039233 10 Manual.Count131072.C051751.packed 64 cuts51751 = true := by
 decide +kernel
def cuts51752 : List PrefixCut := [⟨35,132210798,132210874⟩,
⟨64,242606585,242606725⟩]
theorem checked51752 : checkPrefixCuts (2^48) 6787170305 10 Manual.Count131072.C051752.packed 64 cuts51752 = true := by
 decide +kernel
def pointBounds51752 : List (Nat × Nat × Nat) := [(6787241984,112085305066507,112085692432222)]
theorem point_links_checked51752 : (cuts51752.take 1).map (fun c => (6787170305-1+2*2^10*c.k,112085172855709+c.lower,112085560221348+c.upper)) = pointBounds51752 := by
 decide +kernel
def cuts51753 : List PrefixCut := [⟨64,240486906,240487047⟩]
theorem checked51753 : checkPrefixCuts (2^48) 6787301377 10 Manual.Count131072.C051753.packed 64 cuts51753 = true := by
 decide +kernel
def cuts51754 : List PrefixCut := [⟨11,41552885,41552907⟩,
⟨64,237994101,237994231⟩]
theorem checked51754 : checkPrefixCuts (2^48) 6787432449 10 Manual.Count131072.C051754.packed 64 cuts51754 = true := by
 decide +kernel
def pointBounds51754 : List (Nat × Nat × Nat) := [(6787454976,112085697502085,112086084868027)]
theorem point_links_checked51754 : (cuts51754.take 1).map (fun c => (6787432449-1+2*2^10*c.k,112085655949200+c.lower,112086043315120+c.upper)) = pointBounds51754 := by
 decide +kernel
def cuts51755 : List PrefixCut := [⟨51,191752129,191752240⟩,
⟨64,239482363,239482501⟩]
theorem checked51755 : checkPrefixCuts (2^48) 6787563521 10 Manual.Count131072.C051755.packed 64 cuts51755 = true := by
 decide +kernel
def pointBounds51755 : List (Nat × Nat × Nat) := [(6787667968,112086085695430,112086473061591)]
theorem point_links_checked51755 : (cuts51755.take 1).map (fun c => (6787563521-1+2*2^10*c.k,112085893943301+c.lower,112086281309351+c.upper)) = pointBounds51755 := by
 decide +kernel
def cuts51756 : List PrefixCut := [⟨64,240929133,240929270⟩]
theorem checked51756 : checkPrefixCuts (2^48) 6787694593 10 Manual.Count131072.C051756.packed 64 cuts51756 = true := by
 decide +kernel
def cuts51757 : List PrefixCut := [⟨27,101761092,101761149⟩,
⟨64,239556061,239556194⟩]
theorem checked51757 : checkPrefixCuts (2^48) 6787825665 10 Manual.Count131072.C051757.packed 64 cuts51757 = true := by
 decide +kernel
def pointBounds51757 : List (Nat × Nat × Nat) := [(6787880960,112086476115889,112086863482271)]
theorem point_links_checked51757 : (cuts51757.take 1).map (fun c => (6787825665-1+2*2^10*c.k,112086374354797+c.lower,112086761721122+c.upper)) = pointBounds51757 := by
 decide +kernel
def cuts51758 : List PrefixCut := [⟨64,242412606,242412742⟩]
theorem checked51758 : checkPrefixCuts (2^48) 6787956737 10 Manual.Count131072.C051758.packed 64 cuts51758 = true := by
 decide +kernel
def cuts51759 : List PrefixCut := [⟨3,10573827,10573833⟩,
⟨64,234819722,234819862⟩]
theorem checked51759 : checkPrefixCuts (2^48) 6788087809 10 Manual.Count131072.C051759.packed 64 cuts51759 = true := by
 decide +kernel
def pointBounds51759 : List (Nat × Nat × Nat) := [(6788093952,112086866897291,112087254263891)]
theorem point_links_checked51759 : (cuts51759.take 1).map (fun c => (6788087809-1+2*2^10*c.k,112086856323464+c.lower,112087243690058+c.upper)) = pointBounds51759 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000054
