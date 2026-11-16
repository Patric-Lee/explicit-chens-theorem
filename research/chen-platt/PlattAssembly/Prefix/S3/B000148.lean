import PlattAssemblyKernel
import PlattCertificates.Count131072.C024736
import PlattCertificates.Count131072.C024737
import PlattCertificates.Count131072.C024738
import PlattCertificates.Count131072.C024739
import PlattCertificates.Count131072.C024740
import PlattCertificates.Count131072.C024741
import PlattCertificates.Count131072.C024742
import PlattCertificates.Count131072.C024743
import PlattCertificates.Count131072.C024744
import PlattCertificates.Count131072.C024745
import PlattCertificates.Count131072.C024746
import PlattCertificates.Count131072.C024747
import PlattCertificates.Count131072.C024748
import PlattCertificates.Count131072.C024749
import PlattCertificates.Count131072.C024750
import PlattCertificates.Count131072.C024751
import PlattCertificates.Count131072.C024752
import PlattCertificates.Count131072.C024753
import PlattCertificates.Count131072.C024754
import PlattCertificates.Count131072.C024755
import PlattCertificates.Count131072.C024756
import PlattCertificates.Count131072.C024757
import PlattCertificates.Count131072.C024758
import PlattCertificates.Count131072.C024759
import PlattCertificates.Count131072.C024760
import PlattCertificates.Count131072.C024761
import PlattCertificates.Count131072.C024762
import PlattCertificates.Count131072.C024763
import PlattCertificates.Count131072.C024764
import PlattCertificates.Count131072.C024765
import PlattCertificates.Count131072.C024766
import PlattCertificates.Count131072.C024767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24736 : List PrefixCut := [⟨15,60263962,60263995⟩,
⟨115,461207164,461207426⟩,
⟨128,515572833,515573126⟩]
theorem checked24736 : checkPrefixCuts (2^48) 3246129153 9 Manual.Count131072.C024736.packed 128 cuts24736 = true := by
 decide +kernel
def pointBounds24736 : List (Nat × Nat × Nat) := [(3246144512,102761856730727,102762238670703),(3246246912,102762257673929,102762639614134)]
theorem point_links_checked24736 : (cuts24736.take 2).map (fun c => (3246129153-1+2*2^9*c.k,102761796466765+c.lower,102762178406708+c.upper)) = pointBounds24736 := by
 decide +kernel
def cuts24737 : List PrefixCut := [⟨87,348559161,348559357⟩,
⟨128,514598257,514598548⟩]
theorem checked24737 : checkPrefixCuts (2^48) 3246260225 9 Manual.Count131072.C024737.packed 128 cuts24737 = true := by
 decide +kernel
def pointBounds24737 : List (Nat × Nat × Nat) := [(3246349312,102762660598759,102763042539191)]
theorem point_links_checked24737 : (cuts24737.take 1).map (fun c => (3246260225-1+2*2^9*c.k,102762312039598+c.lower,102762693979834+c.upper)) = pointBounds24737 := by
 decide +kernel
def cuts24738 : List PrefixCut := [⟨59,241641622,241641759⟩,
⟨128,517352026,517352324⟩]
theorem checked24738 : checkPrefixCuts (2^48) 3246391297 9 Manual.Count131072.C024738.packed 128 cuts24738 = true := by
 decide +kernel
def pointBounds24738 : List (Nat × Nat × Nat) := [(3246451712,102763068279477,102763450220141)]
theorem point_links_checked24738 : (cuts24738.take 1).map (fun c => (3246391297-1+2*2^9*c.k,102762826637855+c.lower,102763208578382+c.upper)) = pointBounds24738 := by
 decide +kernel
def cuts24739 : List PrefixCut := [⟨31,126235210,126235284⟩,
⟨128,518458166,518458463⟩]
theorem checked24739 : checkPrefixCuts (2^48) 3246522369 9 Manual.Count131072.C024739.packed 128 cuts24739 = true := by
 decide +kernel
def pointBounds24739 : List (Nat × Nat × Nat) := [(3246554112,102763470225091,102763852165990)]
theorem point_links_checked24739 : (cuts24739.take 1).map (fun c => (3246522369-1+2*2^9*c.k,102763343989881+c.lower,102763725930706+c.upper)) = pointBounds24739 := by
 decide +kernel
def cuts24740 : List PrefixCut := [⟨3,12484353,12484359⟩,
⟨103,414838064,414838301⟩,
⟨128,517830270,517830561⟩]
theorem checked24740 : checkPrefixCuts (2^48) 3246653441 9 Manual.Count131072.C024740.packed 128 cuts24740 = true := by
 decide +kernel
def pointBounds24740 : List (Nat × Nat × Nat) := [(3246656512,102763874932400,102764256873528),(3246758912,102764277286111,102764659227470)]
theorem point_links_checked24740 : (cuts24740.take 2).map (fun c => (3246653441-1+2*2^9*c.k,102763862448047+c.lower,102764244389169+c.upper)) = pointBounds24740 := by
 decide +kernel
def cuts24741 : List PrefixCut := [⟨75,300996029,300996197⟩,
⟨128,516508973,516509266⟩]
theorem checked24741 : checkPrefixCuts (2^48) 3246784513 9 Manual.Count131072.C024741.packed 128 cuts24741 = true := by
 decide +kernel
def pointBounds24741 : List (Nat × Nat × Nat) := [(3246861312,102764681274346,102765063215927)]
theorem point_links_checked24741 : (cuts24741.take 1).map (fun c => (3246784513-1+2*2^9*c.k,102764380278317+c.lower,102764762219730+c.upper)) = pointBounds24741 := by
 decide +kernel
def cuts24742 : List PrefixCut := [⟨47,191323258,191323361⟩,
⟨128,520562540,520562824⟩]
theorem checked24742 : checkPrefixCuts (2^48) 3246915585 9 Manual.Count131072.C024742.packed 128 cuts24742 = true := by
 decide +kernel
def pointBounds24742 : List (Nat × Nat × Nat) := [(3246963712,102765088110548,102765470052357)]
theorem point_links_checked24742 : (cuts24742.take 1).map (fun c => (3246915585-1+2*2^9*c.k,102764896787290+c.lower,102765278728996+c.upper)) = pointBounds24742 := by
 decide +kernel
def cuts24743 : List PrefixCut := [⟨19,76110464,76110506⟩,
⟨119,480580574,480580844⟩,
⟨128,516033945,516034235⟩]
theorem checked24743 : checkPrefixCuts (2^48) 3247046657 9 Manual.Count131072.C024743.packed 128 cuts24743 = true := by
 decide +kernel
def pointBounds24743 : List (Nat × Nat × Nat) := [(3247066112,102765493460294,102765875402326),(3247168512,102765897930404,102766279872664)]
theorem point_links_checked24743 : (cuts24743.take 2).map (fun c => (3247046657-1+2*2^9*c.k,102765417349830+c.lower,102765799291820+c.upper)) = pointBounds24743 := by
 decide +kernel
def cuts24744 : List PrefixCut := [⟨91,374898307,374898522⟩,
⟨128,522774291,522774592⟩]
theorem checked24744 : checkPrefixCuts (2^48) 3247177729 9 Manual.Count131072.C024744.packed 128 cuts24744 = true := by
 decide +kernel
def pointBounds24744 : List (Nat × Nat × Nat) := [(3247270912,102766308282082,102766690224577)]
theorem point_links_checked24744 : (cuts24744.take 1).map (fun c => (3247177729-1+2*2^9*c.k,102765933383775+c.lower,102766315326055+c.upper)) = pointBounds24744 := by
 decide +kernel
def cuts24745 : List PrefixCut := [⟨63,262982823,262982968⟩,
⟨128,522753284,522753575⟩]
theorem checked24745 : checkPrefixCuts (2^48) 3247308801 9 Manual.Count131072.C024745.packed 128 cuts24745 = true := by
 decide +kernel
def pointBounds24745 : List (Nat × Nat × Nat) := [(3247373312,102766719140889,102767101083615)]
theorem point_links_checked24745 : (cuts24745.take 1).map (fun c => (3247308801-1+2*2^9*c.k,102766456158066+c.lower,102766838100647+c.upper)) = pointBounds24745 := by
 decide +kernel
def cuts24746 : List PrefixCut := [⟨35,140500923,140501002⟩,
⟨128,519785082,519785368⟩]
theorem checked24746 : checkPrefixCuts (2^48) 3247439873 9 Manual.Count131072.C024746.packed 128 cuts24746 = true := by
 decide +kernel
def pointBounds24746 : List (Nat × Nat × Nat) := [(3247475712,102767119412273,102767501355224)]
theorem point_links_checked24746 : (cuts24746.take 1).map (fun c => (3247439873-1+2*2^9*c.k,102766978911350+c.lower,102767360854222+c.upper)) = pointBounds24746 := by
 decide +kernel
def cuts24747 : List PrefixCut := [⟨7,28601874,28601890⟩,
⟨107,422694406,422694646⟩,
⟨128,508323600,508323891⟩]
theorem checked24747 : checkPrefixCuts (2^48) 3247570945 9 Manual.Count131072.C024747.packed 128 cuts24747 = true := by
 decide +kernel
def pointBounds24747 : List (Nat × Nat × Nat) := [(3247578112,102767527298306,102767909241480),(3247680512,102767921390838,102768303334236)]
theorem point_links_checked24747 : (cuts24747.take 2).map (fun c => (3247570945-1+2*2^9*c.k,102767498696432+c.lower,102767880639590+c.upper)) = pointBounds24747 := by
 decide +kernel
def cuts24748 : List PrefixCut := [⟨79,322577812,322577993⟩,
⟨128,523729887,523730177⟩]
theorem checked24748 : checkPrefixCuts (2^48) 3247702017 9 Manual.Count131072.C024748.packed 128 cuts24748 = true := by
 decide +kernel
def pointBounds24748 : List (Nat × Nat × Nat) := [(3247782912,102768329597844,102768711541474)]
theorem point_links_checked24748 : (cuts24748.take 1).map (fun c => (3247702017-1+2*2^9*c.k,102768007020032+c.lower,102768388963481+c.upper)) = pointBounds24748 := by
 decide +kernel
def cuts24749 : List PrefixCut := [⟨51,206435453,206435567⟩,
⟨128,518942205,518942494⟩]
theorem checked24749 : checkPrefixCuts (2^48) 3247833089 9 Manual.Count131072.C024749.packed 128 cuts24749 = true := by
 decide +kernel
def pointBounds24749 : List (Nat × Nat × Nat) := [(3247885312,102768737185372,102769119129225)]
theorem point_links_checked24749 : (cuts24749.take 1).map (fun c => (3247833089-1+2*2^9*c.k,102768530749919+c.lower,102768912693658+c.upper)) = pointBounds24749 := by
 decide +kernel
def cuts24750 : List PrefixCut := [⟨23,93161253,93161302⟩,
⟨123,503929357,503929637⟩,
⟨128,525160694,525160986⟩]
theorem checked24750 : checkPrefixCuts (2^48) 3247964161 9 Manual.Count131072.C024750.packed 128 cuts24750 = true := by
 decide +kernel
def pointBounds24750 : List (Nat × Nat × Nat) := [(3247987712,102769142853377,102769524797454),(3248090112,102769553621481,102769935565789)]
theorem point_links_checked24750 : (cuts24750.take 2).map (fun c => (3247964161-1+2*2^9*c.k,102769049692124+c.lower,102769431636152+c.upper)) = pointBounds24750 := by
 decide +kernel
def cuts24751 : List PrefixCut := [⟨95,386837511,386837731⟩,
⟨128,521413341,521413636⟩]
theorem checked24751 : checkPrefixCuts (2^48) 3248095233 9 Manual.Count131072.C024751.packed 128 cuts24751 = true := by
 decide +kernel
def pointBounds24751 : List (Nat × Nat × Nat) := [(3248192512,102769961690329,102770343634869)]
theorem point_links_checked24751 : (cuts24751.take 1).map (fun c => (3248095233-1+2*2^9*c.k,102769574852818+c.lower,102769956797138+c.upper)) = pointBounds24751 := by
 decide +kernel
def cuts24752 : List PrefixCut := [⟨67,272180299,272180454⟩,
⟨128,519919203,519919497⟩]
theorem checked24752 : checkPrefixCuts (2^48) 3248226305 9 Manual.Count131072.C024752.packed 128 cuts24752 = true := by
 decide +kernel
def pointBounds24752 : List (Nat × Nat × Nat) := [(3248294912,102770368446458,102770750391228)]
theorem point_links_checked24752 : (cuts24752.take 1).map (fun c => (3248226305-1+2*2^9*c.k,102770096266159+c.lower,102770478210774+c.upper)) = pointBounds24752 := by
 decide +kernel
def cuts24753 : List PrefixCut := [⟨39,158744493,158744585⟩,
⟨128,523364192,523364498⟩]
theorem checked24753 : checkPrefixCuts (2^48) 3248357377 9 Manual.Count131072.C024753.packed 128 cuts24753 = true := by
 decide +kernel
def pointBounds24753 : List (Nat × Nat × Nat) := [(3248397312,102770774929855,102771156874856)]
theorem point_links_checked24753 : (cuts24753.take 1).map (fun c => (3248357377-1+2*2^9*c.k,102770616185362+c.lower,102770998130271+c.upper)) = pointBounds24753 := by
 decide +kernel
def cuts24754 : List PrefixCut := [⟨11,45230158,45230183⟩,
⟨111,456626808,456627062⟩,
⟨128,524469604,524469897⟩]
theorem checked24754 : checkPrefixCuts (2^48) 3248488449 9 Manual.Count131072.C024754.packed 128 cuts24754 = true := by
 decide +kernel
def pointBounds24754 : List (Nat × Nat × Nat) := [(3248499712,102771184779712,102771566724952),(3248602112,102771596176362,102771978121831)]
theorem point_links_checked24754 : (cuts24754.take 2).map (fun c => (3248488449-1+2*2^9*c.k,102771139549554+c.lower,102771521494769+c.upper)) = pointBounds24754 := by
 decide +kernel
def cuts24755 : List PrefixCut := [⟨83,340335023,340335216⟩,
⟨128,521849138,521849432⟩]
theorem checked24755 : checkPrefixCuts (2^48) 3248619521 9 Manual.Count131072.C024755.packed 128 cuts24755 = true := by
 decide +kernel
def pointBounds24755 : List (Nat × Nat × Nat) := [(3248704512,102772004354181,102772386299882)]
theorem point_links_checked24755 : (cuts24755.take 1).map (fun c => (3248619521-1+2*2^9*c.k,102771664019158+c.lower,102772045964666+c.upper)) = pointBounds24755 := by
 decide +kernel
def cuts24756 : List PrefixCut := [⟨55,218073423,218073546⟩,
⟨128,513337363,513337655⟩]
theorem checked24756 : checkPrefixCuts (2^48) 3248750593 9 Manual.Count131072.C024756.packed 128 cuts24756 = true := by
 decide +kernel
def pointBounds24756 : List (Nat × Nat × Nat) := [(3248806912,102772403941719,102772785887644)]
theorem point_links_checked24756 : (cuts24756.take 1).map (fun c => (3248750593-1+2*2^9*c.k,102772185868296+c.lower,102772567814098+c.upper)) = pointBounds24756 := by
 decide +kernel
def cuts24757 : List PrefixCut := [⟨27,110635573,110635633⟩,
⟨127,511844028,511844318⟩,
⟨128,516782166,516782458⟩]
theorem checked24757 : checkPrefixCuts (2^48) 3248881665 9 Manual.Count131072.C024757.packed 128 cuts24757 = true := by
 decide +kernel
def pointBounds24757 : List (Nat × Nat × Nat) := [(3248909312,102772809841232,102773191787386),(3249011712,102773211049687,102773592996071)]
theorem point_links_checked24757 : (cuts24757.take 2).map (fun c => (3248881665-1+2*2^9*c.k,102772699205659+c.lower,102773081151753+c.upper)) = pointBounds24757 := by
 decide +kernel
def cuts24758 : List PrefixCut := [⟨99,395651190,395651413⟩,
⟨128,513988966,513989255⟩]
theorem checked24758 : checkPrefixCuts (2^48) 3249012737 9 Manual.Count131072.C024758.packed 128 cuts24758 = true := by
 decide +kernel
def pointBounds24758 : List (Nat × Nat × Nat) := [(3249114112,102773611639015,102773993585624)]
theorem point_links_checked24758 : (cuts24758.take 1).map (fun c => (3249012737-1+2*2^9*c.k,102773215987825+c.lower,102773597934211+c.upper)) = pointBounds24758 := by
 decide +kernel
def cuts24759 : List PrefixCut := [⟨71,286483783,286483947⟩,
⟨128,512842135,512842430⟩]
theorem checked24759 : checkPrefixCuts (2^48) 3249143809 9 Manual.Count131072.C024759.packed 128 cuts24759 = true := by
 decide +kernel
def pointBounds24759 : List (Nat × Nat × Nat) := [(3249216512,102774016460574,102774398407413)]
theorem point_links_checked24759 : (cuts24759.take 1).map (fun c => (3249143809-1+2*2^9*c.k,102773729976791+c.lower,102774111923466+c.upper)) = pointBounds24759 := by
 decide +kernel
def cuts24760 : List PrefixCut := [⟨43,171693526,171693624⟩,
⟨128,509443070,509443367⟩]
theorem checked24760 : checkPrefixCuts (2^48) 3249274881 9 Manual.Count131072.C024760.packed 128 cuts24760 = true := by
 decide +kernel
def pointBounds24760 : List (Nat × Nat × Nat) := [(3249318912,102774414512452,102774796459520)]
theorem point_links_checked24760 : (cuts24760.take 1).map (fun c => (3249274881-1+2*2^9*c.k,102774242818926+c.lower,102774624765896+c.upper)) = pointBounds24760 := by
 decide +kernel
def cuts24761 : List PrefixCut := [⟨15,61156042,61156075⟩,
⟨115,466632347,466632604⟩,
⟨128,522502365,522502653⟩]
theorem checked24761 : checkPrefixCuts (2^48) 3249405953 9 Manual.Count131072.C024761.packed 128 cuts24761 = true := by
 decide +kernel
def pointBounds24761 : List (Nat × Nat × Nat) := [(3249421312,102774813418038,102775195365338),(3249523712,102775218894343,102775600841867)]
theorem point_links_checked24761 : (cuts24761.take 2).map (fun c => (3249405953-1+2*2^9*c.k,102774752261996+c.lower,102775134209263+c.upper)) = pointBounds24761 := by
 decide +kernel
def cuts24762 : List PrefixCut := [⟨87,347514617,347514814⟩,
⟨128,511047635,511047921⟩]
theorem checked24762 : checkPrefixCuts (2^48) 3249537025 9 Manual.Count131072.C024762.packed 128 cuts24762 = true := by
 decide +kernel
def pointBounds24762 : List (Nat × Nat × Nat) := [(3249626112,102775622278978,102776004226730)]
theorem point_links_checked24762 : (cuts24762.take 1).map (fun c => (3249537025-1+2*2^9*c.k,102775274764361+c.lower,102775656711916+c.upper)) = pointBounds24762 := by
 decide +kernel
def cuts24763 : List PrefixCut := [⟨59,235854542,235854676⟩,
⟨128,516830216,516830506⟩]
theorem checked24763 : checkPrefixCuts (2^48) 3249668097 9 Manual.Count131072.C024763.packed 128 cuts24763 = true := by
 decide +kernel
def pointBounds24763 : List (Nat × Nat × Nat) := [(3249728512,102776021666538,102776403614513)]
theorem point_links_checked24763 : (cuts24763.take 1).map (fun c => (3249668097-1+2*2^9*c.k,102775785811996+c.lower,102776167759837+c.upper)) = pointBounds24763 := by
 decide +kernel
def cuts24764 : List PrefixCut := [⟨31,126540989,126541056⟩,
⟨128,516029981,516030268⟩]
theorem checked24764 : checkPrefixCuts (2^48) 3249799169 9 Manual.Count131072.C024764.packed 128 cuts24764 = true := by
 decide +kernel
def pointBounds24764 : List (Nat × Nat × Nat) := [(3249830912,102776429183201,102776811131399)]
theorem point_links_checked24764 : (cuts24764.take 1).map (fun c => (3249799169-1+2*2^9*c.k,102776302642212+c.lower,102776684590343+c.upper)) = pointBounds24764 := by
 decide +kernel
def cuts24765 : List PrefixCut := [⟨3,12644983,12644992⟩,
⟨103,418403844,418404082⟩,
⟨128,519386870,519387168⟩]
theorem checked24765 : checkPrefixCuts (2^48) 3249930241 9 Manual.Count131072.C024765.packed 128 cuts24765 = true := by
 decide +kernel
def pointBounds24765 : List (Nat × Nat × Nat) := [(3249933312,102776831317176,102777213265603),(3250035712,102777237076037,102777619024693)]
theorem point_links_checked24765 : (cuts24765.take 2).map (fun c => (3249930241-1+2*2^9*c.k,102776818672193+c.lower,102777200620611+c.upper)) = pointBounds24765 := by
 decide +kernel
def cuts24766 : List PrefixCut := [⟨75,299220293,299220463⟩,
⟨128,516594471,516594760⟩]
theorem checked24766 : checkPrefixCuts (2^48) 3250061313 9 Manual.Count131072.C024766.packed 128 cuts24766 = true := by
 decide +kernel
def pointBounds24766 : List (Nat × Nat × Nat) := [(3250138112,102777637279356,102778019228242)]
theorem point_links_checked24766 : (cuts24766.take 1).map (fun c => (3250061313-1+2*2^9*c.k,102777338059063+c.lower,102777720007779+c.upper)) = pointBounds24766 := by
 decide +kernel
def cuts24767 : List PrefixCut := [⟨47,191043786,191043892⟩,
⟨128,522375929,522376223⟩]
theorem checked24767 : checkPrefixCuts (2^48) 3250192385 9 Manual.Count131072.C024767.packed 128 cuts24767 = true := by
 decide +kernel
def pointBounds24767 : List (Nat × Nat × Nat) := [(3250240512,102778045697320,102778427646431)]
theorem point_links_checked24767 : (cuts24767.take 1).map (fun c => (3250192385-1+2*2^9*c.k,102777854653534+c.lower,102778236602539+c.upper)) = pointBounds24767 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000148
