import PlattAssemblyKernel
import PlattCertificates.Count131072.C049664
import PlattCertificates.Count131072.C049665
import PlattCertificates.Count131072.C049666
import PlattCertificates.Count131072.C049667
import PlattCertificates.Count131072.C049668
import PlattCertificates.Count131072.C049669
import PlattCertificates.Count131072.C049670
import PlattCertificates.Count131072.C049671
import PlattCertificates.Count131072.C049672
import PlattCertificates.Count131072.C049673
import PlattCertificates.Count131072.C049674
import PlattCertificates.Count131072.C049675
import PlattCertificates.Count131072.C049676
import PlattCertificates.Count131072.C049677
import PlattCertificates.Count131072.C049678
import PlattCertificates.Count131072.C049679
import PlattCertificates.Count131072.C049680
import PlattCertificates.Count131072.C049681
import PlattCertificates.Count131072.C049682
import PlattCertificates.Count131072.C049683
import PlattCertificates.Count131072.C049684
import PlattCertificates.Count131072.C049685
import PlattCertificates.Count131072.C049686
import PlattCertificates.Count131072.C049687
import PlattCertificates.Count131072.C049688
import PlattCertificates.Count131072.C049689
import PlattCertificates.Count131072.C049690
import PlattCertificates.Count131072.C049691
import PlattCertificates.Count131072.C049692
import PlattCertificates.Count131072.C049693
import PlattCertificates.Count131072.C049694
import PlattCertificates.Count131072.C049695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000302
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts49664 : List PrefixCut := [⟨64,255349725,255349873⟩]
theorem checked49664 : checkPrefixCuts (2^48) 6513491969 10 Manual.Count131072.C049664.packed 64 cuts49664 = true := by
 decide +kernel
def cuts49665 : List PrefixCut := [⟨34,132620785,132620862⟩,
⟨64,249942980,249943129⟩]
theorem checked49665 : checkPrefixCuts (2^48) 6513623041 10 Manual.Count131072.C049665.packed 64 cuts49665 = true := by
 decide +kernel
def pointBounds49665 : List (Nat × Nat × Nat) := [(6513692672,111573290876022,111573677950461)]
theorem point_links_checked49665 : (cuts49665.take 1).map (fun c => (6513623041-1+2*2^10*c.k,111573158255237+c.lower,111573545329599+c.upper)) = pointBounds49665 := by
 decide +kernel
def cuts49666 : List PrefixCut := [⟨64,249635464,249635608⟩]
theorem checked49666 : checkPrefixCuts (2^48) 6513754113 10 Manual.Count131072.C049666.packed 64 cuts49666 = true := by
 decide +kernel
def cuts49667 : List PrefixCut := [⟨6,24241641,24241654⟩,
⟨64,252698470,252698618⟩]
theorem checked49667 : checkPrefixCuts (2^48) 6513885185 10 Manual.Count131072.C049667.packed 64 cuts49667 = true := by
 decide +kernel
def pointBounds49667 : List (Nat × Nat × Nat) := [(6513897472,111573682075322,111574069149990)]
theorem point_links_checked49667 : (cuts49667.take 1).map (fun c => (6513885185-1+2*2^10*c.k,111573657833681+c.lower,111574044908336+c.upper)) = pointBounds49667 := by
 decide +kernel
def cuts49668 : List PrefixCut := [⟨42,167440181,167440274⟩,
⟨64,255372397,255372540⟩]
theorem checked49668 : checkPrefixCuts (2^48) 6514016257 10 Manual.Count131072.C049668.packed 64 cuts49668 = true := by
 decide +kernel
def pointBounds49668 : List (Nat × Nat × Nat) := [(6514102272,111574077972332,111574465047228)]
theorem point_links_checked49668 : (cuts49668.take 1).map (fun c => (6514016257-1+2*2^10*c.k,111573910532151+c.lower,111574297606954+c.upper)) = pointBounds49668 := by
 decide +kernel
def cuts49669 : List PrefixCut := [⟨64,250009286,250009429⟩]
theorem checked49669 : checkPrefixCuts (2^48) 6514147329 10 Manual.Count131072.C049669.packed 64 cuts49669 = true := by
 decide +kernel
def cuts49670 : List PrefixCut := [⟨14,54183858,54183887⟩,
⟨64,250911624,250911762⟩]
theorem checked49670 : checkPrefixCuts (2^48) 6514278401 10 Manual.Count131072.C049670.packed 64 cuts49670 = true := by
 decide +kernel
def pointBounds49670 : List (Nat × Nat × Nat) := [(6514307072,111574470097692,111574857172810)]
theorem point_links_checked49670 : (cuts49670.take 1).map (fun c => (6514278401-1+2*2^10*c.k,111574415913834+c.lower,111574802988923+c.upper)) = pointBounds49670 := by
 decide +kernel
def cuts49671 : List PrefixCut := [⟨50,194218626,194218735⟩,
⟨64,250172043,250172180⟩]
theorem checked49671 : checkPrefixCuts (2^48) 6514409473 10 Manual.Count131072.C049671.packed 64 cuts49671 = true := by
 decide +kernel
def pointBounds49671 : List (Nat × Nat × Nat) := [(6514511872,111574861044084,111575248119420)]
theorem point_links_checked49671 : (cuts49671.take 1).map (fun c => (6514409473-1+2*2^10*c.k,111574666825458+c.lower,111575053900685+c.upper)) = pointBounds49671 := by
 decide +kernel
def cuts49672 : List PrefixCut := [⟨64,253796413,253796560⟩]
theorem checked49672 : checkPrefixCuts (2^48) 6514540545 10 Manual.Count131072.C049672.packed 64 cuts49672 = true := by
 decide +kernel
def cuts49673 : List PrefixCut := [⟨22,85893841,85893890⟩,
⟨64,249470709,249470849⟩]
theorem checked49673 : checkPrefixCuts (2^48) 6514671617 10 Manual.Count131072.C049673.packed 64 cuts49673 = true := by
 decide +kernel
def pointBounds49673 : List (Nat × Nat × Nat) := [(6514716672,111575256687755,111575643763315)]
theorem point_links_checked49673 : (cuts49673.take 1).map (fun c => (6514671617-1+2*2^10*c.k,111575170793914+c.lower,111575557869425+c.upper)) = pointBounds49673 := by
 decide +kernel
def cuts49674 : List PrefixCut := [⟨58,226610456,226610586⟩,
⟨64,249897740,249897883⟩]
theorem checked49674 : checkPrefixCuts (2^48) 6514802689 10 Manual.Count131072.C049674.packed 64 cuts49674 = true := by
 decide +kernel
def pointBounds49674 : List (Nat × Nat × Nat) := [(6514921472,111575646875079,111576033950860)]
theorem point_links_checked49674 : (cuts49674.take 1).map (fun c => (6514802689-1+2*2^10*c.k,111575420264623+c.lower,111575807340274+c.upper)) = pointBounds49674 := by
 decide +kernel
def cuts49675 : List PrefixCut := [⟨64,249935907,249936047⟩]
theorem checked49675 : checkPrefixCuts (2^48) 6514933761 10 Manual.Count131072.C049675.packed 64 cuts49675 = true := by
 decide +kernel
def cuts49676 : List PrefixCut := [⟨30,117038268,117038337⟩,
⟨64,250362916,250363061⟩]
theorem checked49676 : checkPrefixCuts (2^48) 6515064833 10 Manual.Count131072.C049676.packed 64 cuts49676 = true := by
 decide +kernel
def pointBounds49676 : List (Nat × Nat × Nat) := [(6515126272,111576037136538,111576424212541)]
theorem point_links_checked49676 : (cuts49676.take 1).map (fun c => (6515064833-1+2*2^10*c.k,111575920098270+c.lower,111576307174204+c.upper)) = pointBounds49676 := by
 decide +kernel
def cuts49677 : List PrefixCut := [⟨64,250141894,250142033⟩]
theorem checked49677 : checkPrefixCuts (2^48) 6515195905 10 Manual.Count131072.C049677.packed 64 cuts49677 = true := by
 decide +kernel
def cuts49678 : List PrefixCut := [⟨2,7949159,7949163⟩,
⟨64,253506574,253506710⟩]
theorem checked49678 : checkPrefixCuts (2^48) 6515326977 10 Manual.Count131072.C049678.packed 64 cuts49678 = true := by
 decide +kernel
def pointBounds49678 : List (Nat × Nat × Nat) := [(6515331072,111576428552239,111576815628461)]
theorem point_links_checked49678 : (cuts49678.take 1).map (fun c => (6515326977-1+2*2^10*c.k,111576420603080+c.lower,111576807679298+c.upper)) = pointBounds49678 := by
 decide +kernel
def cuts49679 : List PrefixCut := [⟨38,148567671,148567757⟩,
⟨64,248058186,248058327⟩]
theorem checked49679 : checkPrefixCuts (2^48) 6515458049 10 Manual.Count131072.C049679.packed 64 cuts49679 = true := by
 decide +kernel
def pointBounds49679 : List (Nat × Nat × Nat) := [(6515535872,111576822677325,111577209753765)]
theorem point_links_checked49679 : (cuts49679.take 1).map (fun c => (6515458049-1+2*2^10*c.k,111576674109654+c.lower,111577061186008+c.upper)) = pointBounds49679 := by
 decide +kernel
def cuts49680 : List PrefixCut := [⟨64,247793975,247794116⟩]
theorem checked49680 : checkPrefixCuts (2^48) 6515589121 10 Manual.Count131072.C049680.packed 64 cuts49680 = true := by
 decide +kernel
def cuts49681 : List PrefixCut := [⟨10,40175336,40175360⟩,
⟨64,249819347,249819489⟩]
theorem checked49681 : checkPrefixCuts (2^48) 6515720193 10 Manual.Count131072.C049681.packed 64 cuts49681 = true := by
 decide +kernel
def pointBounds49681 : List (Nat × Nat × Nat) := [(6515740672,111577210137151,111577597213811)]
theorem point_links_checked49681 : (cuts49681.take 1).map (fun c => (6515720193-1+2*2^10*c.k,111577169961815+c.lower,111577557038451+c.upper)) = pointBounds49681 := by
 decide +kernel
def cuts49682 : List PrefixCut := [⟨46,178970019,178970121⟩,
⟨64,248475183,248475326⟩]
theorem checked49682 : checkPrefixCuts (2^48) 6515851265 10 Manual.Count131072.C049682.packed 64 cuts49682 = true := by
 decide +kernel
def pointBounds49682 : List (Nat × Nat × Nat) := [(6515945472,111577598751181,111577985828061)]
theorem point_links_checked49682 : (cuts49682.take 1).map (fun c => (6515851265-1+2*2^10*c.k,111577419781162+c.lower,111577806857940+c.upper)) = pointBounds49682 := by
 decide +kernel
def cuts49683 : List PrefixCut := [⟨64,252703505,252703649⟩]
theorem checked49683 : checkPrefixCuts (2^48) 6515982337 10 Manual.Count131072.C049683.packed 64 cuts49683 = true := by
 decide +kernel
def cuts49684 : List PrefixCut := [⟨18,70799267,70799307⟩,
⟨64,252439251,252439399⟩]
theorem checked49684 : checkPrefixCuts (2^48) 6516113409 10 Manual.Count131072.C049684.packed 64 cuts49684 = true := by
 decide +kernel
def pointBounds49684 : List (Nat × Nat × Nat) := [(6516150272,111577991759117,111578378836222)]
theorem point_links_checked49684 : (cuts49684.take 1).map (fun c => (6516113409-1+2*2^10*c.k,111577920959850+c.lower,111578308036915+c.upper)) = pointBounds49684 := by
 decide +kernel
def cuts49685 : List PrefixCut := [⟨54,210664490,210664610⟩,
⟨64,249108107,249108250⟩]
theorem checked49685 : checkPrefixCuts (2^48) 6516244481 10 Manual.Count131072.C049685.packed 64 cuts49685 = true := by
 decide +kernel
def pointBounds49685 : List (Nat × Nat × Nat) := [(6516355072,111578384063591,111578771140924)]
theorem point_links_checked49685 : (cuts49685.take 1).map (fun c => (6516244481-1+2*2^10*c.k,111578173399101+c.lower,111578560476314+c.upper)) = pointBounds49685 := by
 decide +kernel
def cuts49686 : List PrefixCut := [⟨64,250398974,250399118⟩]
theorem checked49686 : checkPrefixCuts (2^48) 6516375553 10 Manual.Count131072.C049686.packed 64 cuts49686 = true := by
 decide +kernel
def cuts49687 : List PrefixCut := [⟨26,101808171,101808228⟩,
⟨64,251171399,251171538⟩]
theorem checked49687 : checkPrefixCuts (2^48) 6516506625 10 Manual.Count131072.C049687.packed 64 cuts49687 = true := by
 decide +kernel
def pointBounds49687 : List (Nat × Nat × Nat) := [(6516559872,111578774714353,111579161791910)]
theorem point_links_checked49687 : (cuts49687.take 1).map (fun c => (6516506625-1+2*2^10*c.k,111578672906182+c.lower,111579059983682+c.upper)) = pointBounds49687 := by
 decide +kernel
def cuts49688 : List PrefixCut := [⟨62,239072403,239072540⟩,
⟨64,246976615,246976757⟩]
theorem checked49688 : checkPrefixCuts (2^48) 6516637697 10 Manual.Count131072.C049688.packed 64 cuts49688 = true := by
 decide +kernel
def pointBounds49688 : List (Nat × Nat × Nat) := [(6516764672,111579163149984,111579550227760)]
theorem point_links_checked49688 : (cuts49688.take 1).map (fun c => (6516637697-1+2*2^10*c.k,111578924077581+c.lower,111579311155220+c.upper)) = pointBounds49688 := by
 decide +kernel
def cuts49689 : List PrefixCut := [⟨64,254011961,254012113⟩]
theorem checked49689 : checkPrefixCuts (2^48) 6516768769 10 Manual.Count131072.C049689.packed 64 cuts49689 = true := by
 decide +kernel
def cuts49690 : List PrefixCut := [⟨34,133115590,133115667⟩,
⟨64,250465182,250465322⟩]
theorem checked49690 : checkPrefixCuts (2^48) 6516899841 10 Manual.Count131072.C049690.packed 64 cuts49690 = true := by
 decide +kernel
def pointBounds49690 : List (Nat × Nat × Nat) := [(6516969472,111579558181747,111579945259757)]
theorem point_links_checked49690 : (cuts49690.take 1).map (fun c => (6516899841-1+2*2^10*c.k,111579425066157+c.lower,111579812144090+c.upper)) = pointBounds49690 := by
 decide +kernel
def cuts49691 : List PrefixCut := [⟨64,252921995,252922139⟩]
theorem checked49691 : checkPrefixCuts (2^48) 6517030913 10 Manual.Count131072.C049691.packed 64 cuts49691 = true := by
 decide +kernel
def cuts49692 : List PrefixCut := [⟨6,22545053,22545065⟩,
⟨64,251059734,251059871⟩]
theorem checked49692 : checkPrefixCuts (2^48) 6517161985 10 Manual.Count131072.C049692.packed 64 cuts49692 = true := by
 decide +kernel
def pointBounds49692 : List (Nat × Nat × Nat) := [(6517174272,111579950998387,111580338076616)]
theorem point_links_checked49692 : (cuts49692.take 1).map (fun c => (6517161985-1+2*2^10*c.k,111579928453334+c.lower,111580315531551+c.upper)) = pointBounds49692 := by
 decide +kernel
def cuts49693 : List PrefixCut := [⟨42,165498873,165498964⟩,
⟨64,250363701,250363838⟩]
theorem checked49693 : checkPrefixCuts (2^48) 6517293057 10 Manual.Count131072.C049693.packed 64 cuts49693 = true := by
 decide +kernel
def pointBounds49693 : List (Nat × Nat × Nat) := [(6517379072,111580345011941,111580732090386)]
theorem point_links_checked49693 : (cuts49693.take 1).map (fun c => (6517293057-1+2*2^10*c.k,111580179513068+c.lower,111580566591422+c.upper)) = pointBounds49693 := by
 decide +kernel
def cuts49694 : List PrefixCut := [⟨64,253036299,253036448⟩]
theorem checked49694 : checkPrefixCuts (2^48) 6517424129 10 Manual.Count131072.C049694.packed 64 cuts49694 = true := by
 decide +kernel
def cuts49695 : List PrefixCut := [⟨14,54113429,54113462⟩,
⟨64,248798898,248799042⟩]
theorem checked49695 : checkPrefixCuts (2^48) 6517555201 10 Manual.Count131072.C049695.packed 64 cuts49695 = true := by
 decide +kernel
def pointBounds49695 : List (Nat × Nat × Nat) := [(6517583872,111580737026497,111581124105170)]
theorem point_links_checked49695 : (cuts49695.take 1).map (fun c => (6517555201-1+2*2^10*c.k,111580682913068+c.lower,111581069991708+c.upper)) = pointBounds49695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000302
