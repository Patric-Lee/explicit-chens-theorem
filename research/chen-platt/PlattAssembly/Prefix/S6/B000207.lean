import PlattAssemblyKernel
import PlattCertificates.Count131072.C056624
import PlattCertificates.Count131072.C056625
import PlattCertificates.Count131072.C056626
import PlattCertificates.Count131072.C056627
import PlattCertificates.Count131072.C056628
import PlattCertificates.Count131072.C056629
import PlattCertificates.Count131072.C056630
import PlattCertificates.Count131072.C056631
import PlattCertificates.Count131072.C056632
import PlattCertificates.Count131072.C056633
import PlattCertificates.Count131072.C056634
import PlattCertificates.Count131072.C056635
import PlattCertificates.Count131072.C056636
import PlattCertificates.Count131072.C056637
import PlattCertificates.Count131072.C056638
import PlattCertificates.Count131072.C056639
import PlattCertificates.Count131072.C056640
import PlattCertificates.Count131072.C056641
import PlattCertificates.Count131072.C056642
import PlattCertificates.Count131072.C056643
import PlattCertificates.Count131072.C056644
import PlattCertificates.Count131072.C056645
import PlattCertificates.Count131072.C056646
import PlattCertificates.Count131072.C056647
import PlattCertificates.Count131072.C056648
import PlattCertificates.Count131072.C056649
import PlattCertificates.Count131072.C056650
import PlattCertificates.Count131072.C056651
import PlattCertificates.Count131072.C056652
import PlattCertificates.Count131072.C056653
import PlattCertificates.Count131072.C056654
import PlattCertificates.Count131072.C056655
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000207
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts56624 : List PrefixCut := [⟨64,219241920,219242045⟩]
theorem checked56624 : checkPrefixCuts (2^48) 7425753089 10 Manual.Count131072.C056624.packed 64 cuts56624 = true := by
 decide +kernel
def cuts56625 : List PrefixCut := [⟨50,167120065,167120160⟩,
⟨64,216925879,216926002⟩]
theorem checked56625 : checkPrefixCuts (2^48) 7425884161 10 Manual.Count131072.C056625.packed 64 cuts56625 = true := by
 decide +kernel
def pointBounds56625 : List (Nat × Nat × Nat) := [(7425986560,113201324550860,113201712550326)]
theorem point_links_checked56625 : (cuts56625.take 1).map (fun c => (7425884161-1+2*2^10*c.k,113201157430795+c.lower,113201545430166+c.upper)) = pointBounds56625 := by
 decide +kernel
def cuts56626 : List PrefixCut := [⟨64,218589820,218589943⟩]
theorem checked56626 : checkPrefixCuts (2^48) 7426015233 10 Manual.Count131072.C056626.packed 64 cuts56626 = true := by
 decide +kernel
def cuts56627 : List PrefixCut := [⟨36,122426806,122426877⟩,
⟨64,217145657,217145784⟩]
theorem checked56627 : checkPrefixCuts (2^48) 7426146305 10 Manual.Count131072.C056627.packed 64 cuts56627 = true := by
 decide +kernel
def pointBounds56627 : List (Nat × Nat × Nat) := [(7426220032,113201715373300,113202103372988)]
theorem point_links_checked56627 : (cuts56627.take 1).map (fun c => (7426146305-1+2*2^10*c.k,113201592946494+c.lower,113201980946111+c.upper)) = pointBounds56627 := by
 decide +kernel
def cuts56628 : List PrefixCut := [⟨64,220363532,220363654⟩]
theorem checked56628 : checkPrefixCuts (2^48) 7426277377 10 Manual.Count131072.C056628.packed 64 cuts56628 = true := by
 decide +kernel
def cuts56629 : List PrefixCut := [⟨22,76788991,76789034⟩,
⟨64,220245942,220246066⟩]
theorem checked56629 : checkPrefixCuts (2^48) 7426408449 10 Manual.Count131072.C056629.packed 64 cuts56629 = true := by
 decide +kernel
def pointBounds56629 : List (Nat × Nat × Nat) := [(7426453504,113202107244674,113202495244583)]
theorem point_links_checked56629 : (cuts56629.take 1).map (fun c => (7426408449-1+2*2^10*c.k,113202030455683+c.lower,113202418455549+c.upper)) = pointBounds56629 := by
 decide +kernel
def cuts56630 : List PrefixCut := [⟨64,216906748,216906870⟩]
theorem checked56630 : checkPrefixCuts (2^48) 7426539521 10 Manual.Count131072.C056630.packed 64 cuts56630 = true := by
 decide +kernel
def cuts56631 : List PrefixCut := [⟨8,27250465,27250481⟩,
⟨64,218456845,218456971⟩]
theorem checked56631 : checkPrefixCuts (2^48) 7426670593 10 Manual.Count131072.C056631.packed 64 cuts56631 = true := by
 decide +kernel
def pointBounds56631 : List (Nat × Nat × Nat) := [(7426686976,113202494858838,113202882858966)]
theorem point_links_checked56631 : (cuts56631.take 1).map (fun c => (7426670593-1+2*2^10*c.k,113202467608373+c.lower,113202855608485+c.upper)) = pointBounds56631 := by
 decide +kernel
def cuts56632 : List PrefixCut := [⟨58,197494687,197494798⟩,
⟨64,218073976,218074099⟩]
theorem checked56632 : checkPrefixCuts (2^48) 7426801665 10 Manual.Count131072.C056632.packed 64 cuts56632 = true := by
 decide +kernel
def pointBounds56632 : List (Nat × Nat × Nat) := [(7426920448,113202883559905,113203271560254)]
theorem point_links_checked56632 : (cuts56632.take 1).map (fun c => (7426801665-1+2*2^10*c.k,113202686065218+c.lower,113203074065456+c.upper)) = pointBounds56632 := by
 decide +kernel
def cuts56633 : List PrefixCut := [⟨64,220723097,220723221⟩]
theorem checked56633 : checkPrefixCuts (2^48) 7426932737 10 Manual.Count131072.C056633.packed 64 cuts56633 = true := by
 decide +kernel
def cuts56634 : List PrefixCut := [⟨44,148296104,148296191⟩,
⟨64,216171381,216171507⟩]
theorem checked56634 : checkPrefixCuts (2^48) 7427063809 10 Manual.Count131072.C056634.packed 64 cuts56634 = true := by
 decide +kernel
def pointBounds56634 : List (Nat × Nat × Nat) := [(7427153920,113203273158395,113203661158967)]
theorem point_links_checked56634 : (cuts56634.take 1).map (fun c => (7427063809-1+2*2^10*c.k,113203124862291+c.lower,113203512862776+c.upper)) = pointBounds56634 := by
 decide +kernel
def cuts56635 : List PrefixCut := [⟨64,220071032,220071156⟩]
theorem checked56635 : checkPrefixCuts (2^48) 7427194881 10 Manual.Count131072.C056635.packed 64 cuts56635 = true := by
 decide +kernel
def cuts56636 : List PrefixCut := [⟨30,101601979,101602035⟩,
⟨64,219119689,219119811⟩]
theorem checked56636 : checkPrefixCuts (2^48) 7427325953 10 Manual.Count131072.C056636.packed 64 cuts56636 = true := by
 decide +kernel
def pointBounds56636 : List (Nat × Nat × Nat) := [(7427387392,113203662706683,113204050707474)]
theorem point_links_checked56636 : (cuts56636.take 1).map (fun c => (7427325953-1+2*2^10*c.k,113203561104704+c.lower,113203949105439+c.upper)) = pointBounds56636 := by
 decide +kernel
def cuts56637 : List PrefixCut := [⟨64,217524196,217524318⟩]
theorem checked56637 : checkPrefixCuts (2^48) 7427457025 10 Manual.Count131072.C056637.packed 64 cuts56637 = true := by
 decide +kernel
def cuts56638 : List PrefixCut := [⟨16,53812014,53812043⟩,
⟨64,217861406,217861529⟩]
theorem checked56638 : checkPrefixCuts (2^48) 7427588097 10 Manual.Count131072.C056638.packed 64 cuts56638 = true := by
 decide +kernel
def pointBounds56638 : List (Nat × Nat × Nat) := [(7427620864,113204051560603,113204439561611)]
theorem point_links_checked56638 : (cuts56638.take 1).map (fun c => (7427588097-1+2*2^10*c.k,113203997748589+c.lower,113204385749568+c.upper)) = pointBounds56638 := by
 decide +kernel
def cuts56639 : List PrefixCut := [⟨64,217819674,217819799⟩]
theorem checked56639 : checkPrefixCuts (2^48) 7427719169 10 Manual.Count131072.C056639.packed 64 cuts56639 = true := by
 decide +kernel
def cuts56640 : List PrefixCut := [⟨2,6366279,6366283⟩,
⟨64,219104237,219104358⟩]
theorem checked56640 : checkPrefixCuts (2^48) 7427850241 10 Manual.Count131072.C056640.packed 64 cuts56640 = true := by
 decide +kernel
def pointBounds56640 : List (Nat × Nat × Nat) := [(7427854336,113204439795948,113204827797179)]
theorem point_links_checked56640 : (cuts56640.take 1).map (fun c => (7427850241-1+2*2^10*c.k,113204433429669+c.lower,113204821430896+c.upper)) = pointBounds56640 := by
 decide +kernel
def cuts56641 : List PrefixCut := [⟨52,177114646,177114745⟩,
⟨64,217470965,217471087⟩]
theorem checked56641 : checkPrefixCuts (2^48) 7427981313 10 Manual.Count131072.C056641.packed 64 cuts56641 = true := by
 decide +kernel
def pointBounds56641 : List (Nat × Nat × Nat) := [(7428087808,113204829648552,113205217649999)]
theorem point_links_checked56641 : (cuts56641.take 1).map (fun c => (7427981313-1+2*2^10*c.k,113204652533906+c.lower,113205040535254+c.upper)) = pointBounds56641 := by
 decide +kernel
def cuts56642 : List PrefixCut := [⟨64,220005933,220006054⟩]
theorem checked56642 : checkPrefixCuts (2^48) 7428112385 10 Manual.Count131072.C056642.packed 64 cuts56642 = true := by
 decide +kernel
def cuts56643 : List PrefixCut := [⟨38,128947589,128947663⟩,
⟨64,215985495,215985617⟩]
theorem checked56643 : checkPrefixCuts (2^48) 7428243457 10 Manual.Count131072.C056643.packed 64 cuts56643 = true := by
 decide +kernel
def pointBounds56643 : List (Nat × Nat × Nat) := [(7428321280,113205218958393,113205606960058)]
theorem point_links_checked56643 : (cuts56643.take 1).map (fun c => (7428243457-1+2*2^10*c.k,113205090010804+c.lower,113205478012395+c.upper)) = pointBounds56643 := by
 decide +kernel
def cuts56644 : List PrefixCut := [⟨64,218520401,218520528⟩]
theorem checked56644 : checkPrefixCuts (2^48) 7428374529 10 Manual.Count131072.C056644.packed 64 cuts56644 = true := by
 decide +kernel
def cuts56645 : List PrefixCut := [⟨24,80518506,80518551⟩,
⟨64,217569271,217569396⟩]
theorem checked56645 : checkPrefixCuts (2^48) 7428505601 10 Manual.Count131072.C056645.packed 64 cuts56645 = true := by
 decide +kernel
def pointBounds56645 : List (Nat × Nat × Nat) := [(7428554752,113205605035206,113205993037091)]
theorem point_links_checked56645 : (cuts56645.take 1).map (fun c => (7428505601-1+2*2^10*c.k,113205524516700+c.lower,113205912518540+c.upper)) = pointBounds56645 := by
 decide +kernel
def cuts56646 : List PrefixCut := [⟨64,222718506,222718630⟩]
theorem checked56646 : checkPrefixCuts (2^48) 7428636673 10 Manual.Count131072.C056646.packed 64 cuts56646 = true := by
 decide +kernel
def cuts56647 : List PrefixCut := [⟨10,34062927,34062946⟩,
⟨64,219190852,219190971⟩]
theorem checked56647 : checkPrefixCuts (2^48) 7428767745 10 Manual.Count131072.C056647.packed 64 cuts56647 = true := by
 decide +kernel
def pointBounds56647 : List (Nat × Nat × Nat) := [(7428788224,113205998867404,113206386869512)]
theorem point_links_checked56647 : (cuts56647.take 1).map (fun c => (7428767745-1+2*2^10*c.k,113205964804477+c.lower,113206352806566+c.upper)) = pointBounds56647 := by
 decide +kernel
def cuts56648 : List PrefixCut := [⟨60,202326556,202326673⟩,
⟨64,215435989,215436114⟩]
theorem checked56648 : checkPrefixCuts (2^48) 7428898817 10 Manual.Count131072.C056648.packed 64 cuts56648 = true := by
 decide +kernel
def pointBounds56648 : List (Nat × Nat × Nat) := [(7429021696,113206386321885,113206774324210)]
theorem point_links_checked56648 : (cuts56648.take 1).map (fun c => (7428898817-1+2*2^10*c.k,113206183995329+c.lower,113206571997537+c.upper)) = pointBounds56648 := by
 decide +kernel
def cuts56649 : List PrefixCut := [⟨64,223312922,223313045⟩]
theorem checked56649 : checkPrefixCuts (2^48) 7429029889 10 Manual.Count131072.C056649.packed 64 cuts56649 = true := by
 decide +kernel
def cuts56650 : List PrefixCut := [⟨46,155566503,155566592⟩,
⟨64,216375574,216375697⟩]
theorem checked56650 : checkPrefixCuts (2^48) 7429160961 10 Manual.Count131072.C056650.packed 64 cuts56650 = true := by
 decide +kernel
def pointBounds56650 : List (Nat × Nat × Nat) := [(7429255168,113206778310743,113207166313288)]
theorem point_links_checked56650 : (cuts56650.take 1).map (fun c => (7429160961-1+2*2^10*c.k,113206622744240+c.lower,113207010746696+c.upper)) = pointBounds56650 := by
 decide +kernel
def cuts56651 : List PrefixCut := [⟨64,219667910,219668034⟩]
theorem checked56651 : checkPrefixCuts (2^48) 7429292033 10 Manual.Count131072.C056651.packed 64 cuts56651 = true := by
 decide +kernel
def cuts56652 : List PrefixCut := [⟨32,108468600,108468661⟩,
⟨64,217656078,217656198⟩]
theorem checked56652 : checkPrefixCuts (2^48) 7429423105 10 Manual.Count131072.C056652.packed 64 cuts56652 = true := by
 decide +kernel
def pointBounds56652 : List (Nat × Nat × Nat) := [(7429488640,113207167256324,113207555259088)]
theorem point_links_checked56652 : (cuts56652.take 1).map (fun c => (7429423105-1+2*2^10*c.k,113207058787724+c.lower,113207446790427+c.upper)) = pointBounds56652 := by
 decide +kernel
def cuts56653 : List PrefixCut := [⟨64,216364126,216364252⟩]
theorem checked56653 : checkPrefixCuts (2^48) 7429554177 10 Manual.Count131072.C056653.packed 64 cuts56653 = true := by
 decide +kernel
def cuts56654 : List PrefixCut := [⟨18,60919206,60919240⟩,
⟨64,217837817,217837939⟩]
theorem checked56654 : checkPrefixCuts (2^48) 7429685249 10 Manual.Count131072.C056654.packed 64 cuts56654 = true := by
 decide +kernel
def pointBounds56654 : List (Nat × Nat × Nat) := [(7429722112,113207553727134,113207941730117)]
theorem point_links_checked56654 : (cuts56654.take 1).map (fun c => (7429685249-1+2*2^10*c.k,113207492807928+c.lower,113207880810877+c.upper)) = pointBounds56654 := by
 decide +kernel
def cuts56655 : List PrefixCut := [⟨64,217682450,217682569⟩]
theorem checked56655 : checkPrefixCuts (2^48) 7429816321 10 Manual.Count131072.C056655.packed 64 cuts56655 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000207
