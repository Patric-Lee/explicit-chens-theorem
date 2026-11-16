import PlattAssemblyKernel
import PlattCertificates.Count131072.C069952
import PlattCertificates.Count131072.C069953
import PlattCertificates.Count131072.C069954
import PlattCertificates.Count131072.C069955
import PlattCertificates.Count131072.C069956
import PlattCertificates.Count131072.C069957
import PlattCertificates.Count131072.C069958
import PlattCertificates.Count131072.C069959
import PlattCertificates.Count131072.C069960
import PlattCertificates.Count131072.C069961
import PlattCertificates.Count131072.C069962
import PlattCertificates.Count131072.C069963
import PlattCertificates.Count131072.C069964
import PlattCertificates.Count131072.C069965
import PlattCertificates.Count131072.C069966
import PlattCertificates.Count131072.C069967
import PlattCertificates.Count131072.C069968
import PlattCertificates.Count131072.C069969
import PlattCertificates.Count131072.C069970
import PlattCertificates.Count131072.C069971
import PlattCertificates.Count131072.C069972
import PlattCertificates.Count131072.C069973
import PlattCertificates.Count131072.C069974
import PlattCertificates.Count131072.C069975
import PlattCertificates.Count131072.C069976
import PlattCertificates.Count131072.C069977
import PlattCertificates.Count131072.C069978
import PlattCertificates.Count131072.C069979
import PlattCertificates.Count131072.C069980
import PlattCertificates.Count131072.C069981
import PlattCertificates.Count131072.C069982
import PlattCertificates.Count131072.C069983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000311
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69952 : List PrefixCut := [⟨64,176782046,176782153⟩]
theorem checked69952 : checkPrefixCuts (2^48) 9172680705 10 Manual.Count131072.C069952.packed 64 cuts69952 = true := by
 decide +kernel
def cuts69953 : List PrefixCut := [⟨26,71835202,71835241⟩,
⟨64,176503349,176503454⟩]
theorem checked69953 : checkPrefixCuts (2^48) 9172811777 10 Manual.Count131072.C069953.packed 64 cuts69953 = true := by
 decide +kernel
def pointBounds69953 : List (Nat × Nat × Nat) := [(9172865024,115805548952144,115805938452571)]
theorem point_links_checked69953 : (cuts69953.take 1).map (fun c => (9172811777-1+2*2^10*c.k,115805477116942+c.lower,115805866617330+c.upper)) = pointBounds69953 := by
 decide +kernel
def cuts69954 : List PrefixCut := [⟨64,176961116,176961221⟩]
theorem checked69954 : checkPrefixCuts (2^48) 9172942849 10 Manual.Count131072.C069954.packed 64 cuts69954 = true := by
 decide +kernel
def cuts69955 : List PrefixCut := [⟨38,101259757,101259817⟩,
⟨64,174227627,174227730⟩]
theorem checked69955 : checkPrefixCuts (2^48) 9173073921 10 Manual.Count131072.C069955.packed 64 cuts69955 = true := by
 decide +kernel
def pointBounds69955 : List (Nat × Nat × Nat) := [(9173151744,115805931841164,115806321341822)]
theorem point_links_checked69955 : (cuts69955.take 1).map (fun c => (9173073921-1+2*2^10*c.k,115805830581407+c.lower,115806220082005+c.upper)) = pointBounds69955 := by
 decide +kernel
def cuts69956 : List PrefixCut := [⟨64,175022946,175023044⟩]
theorem checked69956 : checkPrefixCuts (2^48) 9173204993 10 Manual.Count131072.C069956.packed 64 cuts69956 = true := by
 decide +kernel
def cuts69957 : List PrefixCut := [⟨50,135223755,135223831⟩,
⟨64,173118047,173118144⟩]
theorem checked69957 : checkPrefixCuts (2^48) 9173336065 10 Manual.Count131072.C069957.packed 64 cuts69957 = true := by
 decide +kernel
def pointBounds69957 : List (Nat × Nat × Nat) := [(9173438464,115806315055735,115806704556610)]
theorem point_links_checked69957 : (cuts69957.take 1).map (fun c => (9173336065-1+2*2^10*c.k,115806179831980+c.lower,115806569332779+c.upper)) = pointBounds69957 := by
 decide +kernel
def cuts69958 : List PrefixCut := [⟨64,176582804,176582900⟩]
theorem checked69958 : checkPrefixCuts (2^48) 9173467137 10 Manual.Count131072.C069958.packed 64 cuts69958 = true := by
 decide +kernel
def cuts69959 : List PrefixCut := [⟨62,170413043,170413140⟩,
⟨64,175322278,175322378⟩]
theorem checked69959 : checkPrefixCuts (2^48) 9173598209 10 Manual.Count131072.C069959.packed 64 cuts69959 = true := by
 decide +kernel
def pointBounds69959 : List (Nat × Nat × Nat) := [(9173725184,115806699945874,115807089446963)]
theorem point_links_checked69959 : (cuts69959.take 1).map (fun c => (9173598209-1+2*2^10*c.k,115806529532831+c.lower,115806919033823+c.upper)) = pointBounds69959 := by
 decide +kernel
def cuts69960 : List PrefixCut := [⟨64,176516389,176516492⟩]
theorem checked69960 : checkPrefixCuts (2^48) 9173729281 10 Manual.Count131072.C069960.packed 64 cuts69960 = true := by
 decide +kernel
def cuts69961 : List PrefixCut := [⟨64,175685438,175685545⟩]
theorem checked69961 : checkPrefixCuts (2^48) 9173860353 10 Manual.Count131072.C069961.packed 64 cuts69961 = true := by
 decide +kernel
def cuts69962 : List PrefixCut := [⟨10,27214760,27214774⟩,
⟨64,174026123,174026227⟩]
theorem checked69962 : checkPrefixCuts (2^48) 9173991425 10 Manual.Count131072.C069962.packed 64 cuts69962 = true := by
 decide +kernel
def pointBounds69962 : List (Nat × Nat × Nat) := [(9174011904,115807084271696,115807473773012)]
theorem point_links_checked69962 : (cuts69962.take 1).map (fun c => (9173991425-1+2*2^10*c.k,115807057056936+c.lower,115807446558238+c.upper)) = pointBounds69962 := by
 decide +kernel
def cuts69963 : List PrefixCut := [⟨64,174852026,174852130⟩]
theorem checked69963 : checkPrefixCuts (2^48) 9174122497 10 Manual.Count131072.C069963.packed 64 cuts69963 = true := by
 decide +kernel
def cuts69964 : List PrefixCut := [⟨22,58784572,58784609⟩,
⟨64,174757485,174757588⟩]
theorem checked69964 : checkPrefixCuts (2^48) 9174253569 10 Manual.Count131072.C069964.packed 64 cuts69964 = true := by
 decide +kernel
def pointBounds69964 : List (Nat × Nat × Nat) := [(9174298624,115807464719657,115807854221204)]
theorem point_links_checked69964 : (cuts69964.take 1).map (fun c => (9174253569-1+2*2^10*c.k,115807405935085+c.lower,115807795436595+c.upper)) = pointBounds69964 := by
 decide +kernel
def cuts69965 : List PrefixCut := [⟨64,177945755,177945856⟩]
theorem checked69965 : checkPrefixCuts (2^48) 9174384641 10 Manual.Count131072.C069965.packed 64 cuts69965 = true := by
 decide +kernel
def cuts69966 : List PrefixCut := [⟨34,94218171,94218226⟩,
⟨64,174261630,174261727⟩]
theorem checked69966 : checkPrefixCuts (2^48) 9174515713 10 Manual.Count131072.C069966.packed 64 cuts69966 = true := by
 decide +kernel
def pointBounds69966 : List (Nat × Nat × Nat) := [(9174585344,115807852856496,115808242358265)]
theorem point_links_checked69966 : (cuts69966.take 1).map (fun c => (9174515713-1+2*2^10*c.k,115807758638325+c.lower,115808148140039+c.upper)) = pointBounds69966 := by
 decide +kernel
def cuts69967 : List PrefixCut := [⟨64,175578351,175578459⟩]
theorem checked69967 : checkPrefixCuts (2^48) 9174646785 10 Manual.Count131072.C069967.packed 64 cuts69967 = true := by
 decide +kernel
def cuts69968 : List PrefixCut := [⟨46,127655516,127655592⟩,
⟨64,177324539,177324643⟩]
theorem checked69968 : checkPrefixCuts (2^48) 9174777857 10 Manual.Count131072.C069968.packed 64 cuts69968 = true := by
 decide +kernel
def pointBounds69968 : List (Nat × Nat × Nat) := [(9174872064,115808236133822,115808625635817)]
theorem point_links_checked69968 : (cuts69968.take 1).map (fun c => (9174777857-1+2*2^10*c.k,115808108478306+c.lower,115808497980225+c.upper)) = pointBounds69968 := by
 decide +kernel
def cuts69969 : List PrefixCut := [⟨64,175818750,175818847⟩]
theorem checked69969 : checkPrefixCuts (2^48) 9174908929 10 Manual.Count131072.C069969.packed 64 cuts69969 = true := by
 decide +kernel
def cuts69970 : List PrefixCut := [⟨58,159648990,159649080⟩,
⟨64,175632182,175632280⟩]
theorem checked69970 : checkPrefixCuts (2^48) 9175040001 10 Manual.Count131072.C069970.packed 64 cuts69970 = true := by
 decide +kernel
def pointBounds69970 : List (Nat × Nat × Nat) := [(9175158784,115808621270585,115809010772795)]
theorem point_links_checked69970 : (cuts69970.take 1).map (fun c => (9175040001-1+2*2^10*c.k,115808461621595+c.lower,115808851123715+c.upper)) = pointBounds69970 := by
 decide +kernel
def cuts69971 : List PrefixCut := [⟨64,173696985,173697079⟩]
theorem checked69971 : checkPrefixCuts (2^48) 9175171073 10 Manual.Count131072.C069971.packed 64 cuts69971 = true := by
 decide +kernel
def cuts69972 : List PrefixCut := [⟨64,176762220,176762326⟩]
theorem checked69972 : checkPrefixCuts (2^48) 9175302145 10 Manual.Count131072.C069972.packed 64 cuts69972 = true := by
 decide +kernel
def cuts69973 : List PrefixCut := [⟨7,19326504,19326516⟩,
⟨64,175041795,175041900⟩]
theorem checked69973 : checkPrefixCuts (2^48) 9175433217 10 Manual.Count131072.C069973.packed 64 cuts69973 = true := by
 decide +kernel
def pointBounds69973 : List (Nat × Nat × Nat) := [(9175447552,115809007039486,115809396541916)]
theorem point_links_checked69973 : (cuts69973.take 1).map (fun c => (9175433217-1+2*2^10*c.k,115808987712982+c.lower,115809377215400+c.upper)) = pointBounds69973 := by
 decide +kernel
def cuts69974 : List PrefixCut := [⟨64,175836880,175836984⟩]
theorem checked69974 : checkPrefixCuts (2^48) 9175564289 10 Manual.Count131072.C069974.packed 64 cuts69974 = true := by
 decide +kernel
def cuts69975 : List PrefixCut := [⟨20,54879488,54879519⟩,
⟨64,176417201,176417300⟩]
theorem checked69975 : checkPrefixCuts (2^48) 9175695361 10 Manual.Count131072.C069975.packed 64 cuts69975 = true := by
 decide +kernel
def pointBounds69975 : List (Nat × Nat × Nat) := [(9175736320,115809393471145,115809782973803)]
theorem point_links_checked69975 : (cuts69975.take 1).map (fun c => (9175695361-1+2*2^10*c.k,115809338591657+c.lower,115809728094284+c.upper)) = pointBounds69975 := by
 decide +kernel
def cuts69976 : List PrefixCut := [⟨64,177058874,177058976⟩]
theorem checked69976 : checkPrefixCuts (2^48) 9175826433 10 Manual.Count131072.C069976.packed 64 cuts69976 = true := by
 decide +kernel
def cuts69977 : List PrefixCut := [⟨33,90399662,90399717⟩,
⟨64,175307865,175307971⟩]
theorem checked69977 : checkPrefixCuts (2^48) 9175957505 10 Manual.Count131072.C069977.packed 64 cuts69977 = true := by
 decide +kernel
def pointBounds69977 : List (Nat × Nat × Nat) := [(9176025088,115809782467394,115810171970277)]
theorem point_links_checked69977 : (cuts69977.take 1).map (fun c => (9175957505-1+2*2^10*c.k,115809692067732+c.lower,115810081570560+c.upper)) = pointBounds69977 := by
 decide +kernel
def cuts69978 : List PrefixCut := [⟨64,173771633,173771735⟩]
theorem checked69978 : checkPrefixCuts (2^48) 9176088577 10 Manual.Count131072.C069978.packed 64 cuts69978 = true := by
 decide +kernel
def cuts69979 : List PrefixCut := [⟨46,126807255,126807333⟩,
⟨64,176775215,176775322⟩]
theorem checked69979 : checkPrefixCuts (2^48) 9176219649 10 Manual.Count131072.C069979.packed 64 cuts69979 = true := by
 decide +kernel
def pointBounds69979 : List (Nat × Nat × Nat) := [(9176313856,115810167954485,115810557457599)]
theorem point_links_checked69979 : (cuts69979.take 1).map (fun c => (9176219649-1+2*2^10*c.k,115810041147230+c.lower,115810430650266+c.upper)) = pointBounds69979 := by
 decide +kernel
def cuts69980 : List PrefixCut := [⟨64,177416839,177416947⟩]
theorem checked69980 : checkPrefixCuts (2^48) 9176350721 10 Manual.Count131072.C069980.packed 64 cuts69980 = true := by
 decide +kernel
def cuts69981 : List PrefixCut := [⟨59,160636113,160636200⟩,
⟨64,175328523,175328617⟩]
theorem checked69981 : checkPrefixCuts (2^48) 9176481793 10 Manual.Count131072.C069981.packed 64 cuts69981 = true := by
 decide +kernel
def pointBounds69981 : List (Nat × Nat × Nat) := [(9176602624,115810555975397,115810945478735)]
theorem point_links_checked69981 : (cuts69981.take 1).map (fun c => (9176481793-1+2*2^10*c.k,115810395339284+c.lower,115810784842535+c.upper)) = pointBounds69981 := by
 decide +kernel
def cuts69982 : List PrefixCut := [⟨64,177810518,177810622⟩]
theorem checked69982 : checkPrefixCuts (2^48) 9176612865 10 Manual.Count131072.C069982.packed 64 cuts69982 = true := by
 decide +kernel
def cuts69983 : List PrefixCut := [⟨64,176765115,176765220⟩]
theorem checked69983 : checkPrefixCuts (2^48) 9176743937 10 Manual.Count131072.C069983.packed 64 cuts69983 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000311
