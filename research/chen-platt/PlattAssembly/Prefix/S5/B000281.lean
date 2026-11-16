import PlattAssemblyKernel
import PlattCertificates.Count131072.C048992
import PlattCertificates.Count131072.C048993
import PlattCertificates.Count131072.C048994
import PlattCertificates.Count131072.C048995
import PlattCertificates.Count131072.C048996
import PlattCertificates.Count131072.C048997
import PlattCertificates.Count131072.C048998
import PlattCertificates.Count131072.C048999
import PlattCertificates.Count131072.C049000
import PlattCertificates.Count131072.C049001
import PlattCertificates.Count131072.C049002
import PlattCertificates.Count131072.C049003
import PlattCertificates.Count131072.C049004
import PlattCertificates.Count131072.C049005
import PlattCertificates.Count131072.C049006
import PlattCertificates.Count131072.C049007
import PlattCertificates.Count131072.C049008
import PlattCertificates.Count131072.C049009
import PlattCertificates.Count131072.C049010
import PlattCertificates.Count131072.C049011
import PlattCertificates.Count131072.C049012
import PlattCertificates.Count131072.C049013
import PlattCertificates.Count131072.C049014
import PlattCertificates.Count131072.C049015
import PlattCertificates.Count131072.C049016
import PlattCertificates.Count131072.C049017
import PlattCertificates.Count131072.C049018
import PlattCertificates.Count131072.C049019
import PlattCertificates.Count131072.C049020
import PlattCertificates.Count131072.C049021
import PlattCertificates.Count131072.C049022
import PlattCertificates.Count131072.C049023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000281
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48992 : List PrefixCut := [⟨16,64658256,64658292⟩,
⟨64,255783647,255783792⟩]
theorem checked48992 : checkPrefixCuts (2^48) 6425411585 10 Manual.Count131072.C048992.packed 64 cuts48992 = true := by
 decide +kernel
def pointBounds48992 : List (Nat × Nat × Nat) := [(6425444352,111403333758877,111403720736437)]
theorem point_links_checked48992 : (cuts48992.take 1).map (fun c => (6425411585-1+2*2^10*c.k,111403269100621+c.lower,111403656078145+c.upper)) = pointBounds48992 := by
 decide +kernel
def cuts48993 : List PrefixCut := [⟨51,200628119,200628234⟩,
⟨64,252755852,252755997⟩]
theorem checked48993 : checkPrefixCuts (2^48) 6425542657 10 Manual.Count131072.C048993.packed 64 cuts48993 = true := by
 decide +kernel
def pointBounds48993 : List (Nat × Nat × Nat) := [(6425647104,111403725512387,111404112490171)]
theorem point_links_checked48993 : (cuts48993.take 1).map (fun c => (6425542657-1+2*2^10*c.k,111403524884268+c.lower,111403911861937+c.upper)) = pointBounds48993 := by
 decide +kernel
def cuts48994 : List PrefixCut := [⟨64,251392763,251392906⟩]
theorem checked48994 : checkPrefixCuts (2^48) 6425673729 10 Manual.Count131072.C048994.packed 64 cuts48994 = true := by
 decide +kernel
def cuts48995 : List PrefixCut := [⟨22,87782576,87782627⟩,
⟨64,253095981,253096126⟩]
theorem checked48995 : checkPrefixCuts (2^48) 6425804801 10 Manual.Count131072.C048995.packed 64 cuts48995 = true := by
 decide +kernel
def pointBounds48995 : List (Nat × Nat × Nat) := [(6425849856,111404116815459,111404503793467)]
theorem point_links_checked48995 : (cuts48995.take 1).map (fun c => (6425804801-1+2*2^10*c.k,111404029032883+c.lower,111404416010840+c.upper)) = pointBounds48995 := by
 decide +kernel
def cuts48996 : List PrefixCut := [⟨57,227028581,227028705⟩,
⟨64,254054476,254054615⟩]
theorem checked48996 : checkPrefixCuts (2^48) 6425935873 10 Manual.Count131072.C048996.packed 64 cuts48996 = true := by
 decide +kernel
def pointBounds48996 : List (Nat × Nat × Nat) := [(6426052608,111404509157445,111404896135671)]
theorem point_links_checked48996 : (cuts48996.take 1).map (fun c => (6425935873-1+2*2^10*c.k,111404282128864+c.lower,111404669106966+c.upper)) = pointBounds48996 := by
 decide +kernel
def cuts48997 : List PrefixCut := [⟨64,253436072,253436212⟩]
theorem checked48997 : checkPrefixCuts (2^48) 6426066945 10 Manual.Count131072.C048997.packed 64 cuts48997 = true := by
 decide +kernel
def cuts48998 : List PrefixCut := [⟨28,113225476,113225543⟩,
⟨64,256891163,256891309⟩]
theorem checked48998 : checkPrefixCuts (2^48) 6426198017 10 Manual.Count131072.C048998.packed 64 cuts48998 = true := by
 decide +kernel
def pointBounds48998 : List (Nat × Nat × Nat) := [(6426255360,111404902844888,111405289823336)]
theorem point_links_checked48998 : (cuts48998.take 1).map (fun c => (6426198017-1+2*2^10*c.k,111404789619412+c.lower,111405176597793+c.upper)) = pointBounds48998 := by
 decide +kernel
def cuts48999 : List PrefixCut := [⟨63,245760818,245760963⟩,
⟨64,249790361,249790508⟩]
theorem checked48999 : checkPrefixCuts (2^48) 6426329089 10 Manual.Count131072.C048999.packed 64 cuts48999 = true := by
 decide +kernel
def pointBounds48999 : List (Nat × Nat × Nat) := [(6426458112,111405292271393,111405679250065)]
theorem point_links_checked48999 : (cuts48999.take 1).map (fun c => (6426329089-1+2*2^10*c.k,111405046510575+c.lower,111405433489102+c.upper)) = pointBounds48999 := by
 decide +kernel
def cuts49000 : List PrefixCut := [⟨64,254515526,254515667⟩]
theorem checked49000 : checkPrefixCuts (2^48) 6426460161 10 Manual.Count131072.C049000.packed 64 cuts49000 = true := by
 decide +kernel
def cuts49001 : List PrefixCut := [⟨34,134898574,134898649⟩,
⟨64,250130560,250130701⟩]
theorem checked49001 : checkPrefixCuts (2^48) 6426591233 10 Manual.Count131072.C049001.packed 64 cuts49001 = true := by
 decide +kernel
def pointBounds49001 : List (Nat × Nat × Nat) := [(6426660864,111405685715036,111406072693926)]
theorem point_links_checked49001 : (cuts49001.take 1).map (fun c => (6426591233-1+2*2^10*c.k,111405550816462+c.lower,111405937795277+c.upper)) = pointBounds49001 := by
 decide +kernel
def cuts49002 : List PrefixCut := [⟨64,254855541,254855688⟩]
theorem checked49002 : checkPrefixCuts (2^48) 6426722305 10 Manual.Count131072.C049002.packed 64 cuts49002 = true := by
 decide +kernel
def cuts49003 : List PrefixCut := [⟨5,19577103,19577115⟩,
⟨64,256383183,256383331⟩]
theorem checked49003 : checkPrefixCuts (2^48) 6426853377 10 Manual.Count131072.C049003.packed 64 cuts49003 = true := by
 decide +kernel
def pointBounds49003 : List (Nat × Nat × Nat) := [(6426863616,111406075379666,111406462358781)]
theorem point_links_checked49003 : (cuts49003.take 1).map (fun c => (6426853377-1+2*2^10*c.k,111406055802563+c.lower,111406442781666+c.upper)) = pointBounds49003 := by
 decide +kernel
def cuts49004 : List PrefixCut := [⟨40,160641943,160642037⟩,
⟨64,253268511,253268655⟩]
theorem checked49004 : checkPrefixCuts (2^48) 6426984449 10 Manual.Count131072.C049004.packed 64 cuts49004 = true := by
 decide +kernel
def pointBounds49004 : List (Nat × Nat × Nat) := [(6427066368,111406472827689,111406859807034)]
theorem point_links_checked49004 : (cuts49004.take 1).map (fun c => (6426984449-1+2*2^10*c.k,111406312185746+c.lower,111406699164997+c.upper)) = pointBounds49004 := by
 decide +kernel
def cuts49005 : List PrefixCut := [⟨64,254796135,254796279⟩]
theorem checked49005 : checkPrefixCuts (2^48) 6427115521 10 Manual.Count131072.C049005.packed 64 cuts49005 = true := by
 decide +kernel
def cuts49006 : List PrefixCut := [⟨11,43487376,43487398⟩,
⟨64,252163327,252163472⟩]
theorem checked49006 : checkPrefixCuts (2^48) 6427246593 10 Manual.Count131072.C049006.packed 64 cuts49006 = true := by
 decide +kernel
def pointBounds49006 : List (Nat × Nat × Nat) := [(6427269120,111406863737768,111407250717329)]
theorem point_links_checked49006 : (cuts49006.take 1).map (fun c => (6427246593-1+2*2^10*c.k,111406820250392+c.lower,111407207229931+c.upper)) = pointBounds49006 := by
 decide +kernel
def cuts49007 : List PrefixCut := [⟨46,184148701,184148806⟩,
⟨64,257763640,257763786⟩]
theorem checked49007 : checkPrefixCuts (2^48) 6427377665 10 Manual.Count131072.C049007.packed 64 cuts49007 = true := by
 decide +kernel
def pointBounds49007 : List (Nat × Nat × Nat) := [(6427471872,111407256562420,111407643542209)]
theorem point_links_checked49007 : (cuts49007.take 1).map (fun c => (6427377665-1+2*2^10*c.k,111407072413719+c.lower,111407459393403+c.upper)) = pointBounds49007 := by
 decide +kernel
def cuts49008 : List PrefixCut := [⟨64,248824884,248825027⟩]
theorem checked49008 : checkPrefixCuts (2^48) 6427508737 10 Manual.Count131072.C049008.packed 64 cuts49008 = true := by
 decide +kernel
def cuts49009 : List PrefixCut := [⟨17,67963961,67964001⟩,
⟨64,254337454,254337598⟩]
theorem checked49009 : checkPrefixCuts (2^48) 6427639809 10 Manual.Count131072.C049009.packed 64 cuts49009 = true := by
 decide +kernel
def pointBounds49009 : List (Nat × Nat × Nat) := [(6427674624,111407646966204,111408033946217)]
theorem point_links_checked49009 : (cuts49009.take 1).map (fun c => (6427639809-1+2*2^10*c.k,111407579002243+c.lower,111407965982216+c.upper)) = pointBounds49009 := by
 decide +kernel
def cuts49010 : List PrefixCut := [⟨52,205156500,205156615⟩,
⟨64,252274140,252274282⟩]
theorem checked49010 : checkPrefixCuts (2^48) 6427770881 10 Manual.Count131072.C049010.packed 64 cuts49010 = true := by
 decide +kernel
def pointBounds49010 : List (Nat × Nat × Nat) := [(6427877376,111408038496197,111408425476429)]
theorem point_links_checked49010 : (cuts49010.take 1).map (fun c => (6427770881-1+2*2^10*c.k,111407833339697+c.lower,111408220319814+c.upper)) = pointBounds49010 := by
 decide +kernel
def cuts49011 : List PrefixCut := [⟨64,256341371,256341515⟩]
theorem checked49011 : checkPrefixCuts (2^48) 6427901953 10 Manual.Count131072.C049011.packed 64 cuts49011 = true := by
 decide +kernel
def cuts49012 : List PrefixCut := [⟨23,91517947,91518002⟩,
⟨64,256555077,256555224⟩]
theorem checked49012 : checkPrefixCuts (2^48) 6428033025 10 Manual.Count131072.C049012.packed 64 cuts49012 = true := by
 decide +kernel
def pointBounds49012 : List (Nat × Nat × Nat) := [(6428080128,111408433473155,111408820453613)]
theorem point_links_checked49012 : (cuts49012.take 1).map (fun c => (6428033025-1+2*2^10*c.k,111408341955208+c.lower,111408728935611+c.upper)) = pointBounds49012 := by
 decide +kernel
def cuts49013 : List PrefixCut := [⟨58,231328594,231328731⟩,
⟨64,255280033,255280183⟩]
theorem checked49013 : checkPrefixCuts (2^48) 6428164097 10 Manual.Count131072.C049013.packed 64 cuts49013 = true := by
 decide +kernel
def pointBounds49013 : List (Nat × Nat × Nat) := [(6428282880,111408829838879,111409216819566)]
theorem point_links_checked49013 : (cuts49013.take 1).map (fun c => (6428164097-1+2*2^10*c.k,111408598510285+c.lower,111408985490835+c.upper)) = pointBounds49013 := by
 decide +kernel
def cuts49014 : List PrefixCut := [⟨64,257683064,257683206⟩]
theorem checked49014 : checkPrefixCuts (2^48) 6428295169 10 Manual.Count131072.C049014.packed 64 cuts49014 = true := by
 decide +kernel
def cuts49015 : List PrefixCut := [⟨29,118177793,118177861⟩,
⟨64,258465963,258466109⟩]
theorem checked49015 : checkPrefixCuts (2^48) 6428426241 10 Manual.Count131072.C049015.packed 64 cuts49015 = true := by
 decide +kernel
def pointBounds49015 : List (Nat × Nat × Nat) := [(6428485632,111409229651175,111409616632085)]
theorem point_links_checked49015 : (cuts49015.take 1).map (fun c => (6428426241-1+2*2^10*c.k,111409111473382+c.lower,111409498454224+c.upper)) = pointBounds49015 := by
 decide +kernel
def cuts49016 : List PrefixCut := [⟨64,253250306,253250454⟩]
theorem checked49016 : checkPrefixCuts (2^48) 6428557313 10 Manual.Count131072.C049016.packed 64 cuts49016 = true := by
 decide +kernel
def pointBounds49016 : List (Nat × Nat × Nat) := [(6428688384,111409623189651,111410010170787)]
theorem point_links_checked49016 : (cuts49016.take 1).map (fun c => (6428557313-1+2*2^10*c.k,111409369939345+c.lower,111409756920333+c.upper)) = pointBounds49016 := by
 decide +kernel
def cuts49017 : List PrefixCut := [⟨64,254295962,254296106⟩]
theorem checked49017 : checkPrefixCuts (2^48) 6428688385 10 Manual.Count131072.C049017.packed 64 cuts49017 = true := by
 decide +kernel
def cuts49018 : List PrefixCut := [⟨35,139536582,139536660⟩,
⟨64,255166429,255166575⟩]
theorem checked49018 : checkPrefixCuts (2^48) 6428819457 10 Manual.Count131072.C049018.packed 64 cuts49018 = true := by
 decide +kernel
def pointBounds49018 : List (Nat × Nat × Nat) := [(6428891136,111410017022195,111410404003553)]
theorem point_links_checked49018 : (cuts49018.take 1).map (fun c => (6428819457-1+2*2^10*c.k,111409877485613+c.lower,111410264466893+c.upper)) = pointBounds49018 := by
 decide +kernel
def cuts49019 : List PrefixCut := [⟨64,252402968,252403114⟩]
theorem checked49019 : checkPrefixCuts (2^48) 6428950529 10 Manual.Count131072.C049019.packed 64 cuts49019 = true := by
 decide +kernel
def cuts49020 : List PrefixCut := [⟨6,23554430,23554443⟩,
⟨64,255243571,255243717⟩]
theorem checked49020 : checkPrefixCuts (2^48) 6429081601 10 Manual.Count131072.C049020.packed 64 cuts49020 = true := by
 decide +kernel
def pointBounds49020 : List (Nat × Nat × Nat) := [(6429093888,111410408609440,111410795591025)]
theorem point_links_checked49020 : (cuts49020.take 1).map (fun c => (6429081601-1+2*2^10*c.k,111410385055010+c.lower,111410772036582+c.upper)) = pointBounds49020 := by
 decide +kernel
def cuts49021 : List PrefixCut := [⟨41,162950391,162950487⟩,
⟨64,254581691,254581838⟩]
theorem checked49021 : checkPrefixCuts (2^48) 6429212673 10 Manual.Count131072.C049021.packed 64 cuts49021 = true := by
 decide +kernel
def pointBounds49021 : List (Nat × Nat × Nat) := [(6429296640,111410803248972,111411190230786)]
theorem point_links_checked49021 : (cuts49021.take 1).map (fun c => (6429212673-1+2*2^10*c.k,111410640298581+c.lower,111411027280299+c.upper)) = pointBounds49021 := by
 decide +kernel
def cuts49022 : List PrefixCut := [⟨64,253657131,253657279⟩]
theorem checked49022 : checkPrefixCuts (2^48) 6429343745 10 Manual.Count131072.C049022.packed 64 cuts49022 = true := by
 decide +kernel
def cuts49023 : List PrefixCut := [⟨12,49294869,49294897⟩,
⟨64,253870873,253871014⟩]
theorem checked49023 : checkPrefixCuts (2^48) 6429474817 10 Manual.Count131072.C049023.packed 64 cuts49023 = true := by
 decide +kernel
def pointBounds49023 : List (Nat × Nat × Nat) := [(6429499392,111411197832272,111411584814313)]
theorem point_links_checked49023 : (cuts49023.take 1).map (fun c => (6429474817-1+2*2^10*c.k,111411148537403+c.lower,111411535519416+c.upper)) = pointBounds49023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000281
