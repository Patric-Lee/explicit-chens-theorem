import PlattAssemblyKernel
import PlattCertificates.Count131072.C050096
import PlattCertificates.Count131072.C050097
import PlattCertificates.Count131072.C050098
import PlattCertificates.Count131072.C050099
import PlattCertificates.Count131072.C050100
import PlattCertificates.Count131072.C050101
import PlattCertificates.Count131072.C050102
import PlattCertificates.Count131072.C050103
import PlattCertificates.Count131072.C050104
import PlattCertificates.Count131072.C050105
import PlattCertificates.Count131072.C050106
import PlattCertificates.Count131072.C050107
import PlattCertificates.Count131072.C050108
import PlattCertificates.Count131072.C050109
import PlattCertificates.Count131072.C050110
import PlattCertificates.Count131072.C050111
import PlattCertificates.Count131072.C050112
import PlattCertificates.Count131072.C050113
import PlattCertificates.Count131072.C050114
import PlattCertificates.Count131072.C050115
import PlattCertificates.Count131072.C050116
import PlattCertificates.Count131072.C050117
import PlattCertificates.Count131072.C050118
import PlattCertificates.Count131072.C050119
import PlattCertificates.Count131072.C050120
import PlattCertificates.Count131072.C050121
import PlattCertificates.Count131072.C050122
import PlattCertificates.Count131072.C050123
import PlattCertificates.Count131072.C050124
import PlattCertificates.Count131072.C050125
import PlattCertificates.Count131072.C050126
import PlattCertificates.Count131072.C050127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50096 : List PrefixCut := [⟨29,113744198,113744262⟩,
⟨64,246465857,246465999⟩]
theorem checked50096 : checkPrefixCuts (2^48) 6570115073 10 Manual.Count131072.C050096.packed 64 cuts50096 = true := by
 decide +kernel
def pointBounds50096 : List (Nat × Nat × Nat) := [(6570174464,111680832620583,111681219756311)]
theorem point_links_checked50096 : (cuts50096.take 1).map (fun c => (6570115073-1+2*2^10*c.k,111680718876385+c.lower,111681106012049+c.upper)) = pointBounds50096 := by
 decide +kernel
def cuts50097 : List PrefixCut := [⟨64,248988505,248988647⟩]
theorem checked50097 : checkPrefixCuts (2^48) 6570246145 10 Manual.Count131072.C050097.packed 64 cuts50097 = true := by
 decide +kernel
def cuts50098 : List PrefixCut := [⟨2,6811557,6811561⟩,
⟨64,243328683,243328825⟩]
theorem checked50098 : checkPrefixCuts (2^48) 6570377217 10 Manual.Count131072.C050098.packed 64 cuts50098 = true := by
 decide +kernel
def pointBounds50098 : List (Nat × Nat × Nat) := [(6570381312,111681221142304,111681608278256)]
theorem point_links_checked50098 : (cuts50098.take 1).map (fun c => (6570377217-1+2*2^10*c.k,111681214330747+c.lower,111681601466695+c.upper)) = pointBounds50098 := by
 decide +kernel
def cuts50099 : List PrefixCut := [⟨39,149764714,149764795⟩,
⟨64,244651886,244652021⟩]
theorem checked50099 : checkPrefixCuts (2^48) 6570508289 10 Manual.Count131072.C050099.packed 64 cuts50099 = true := by
 decide +kernel
def pointBounds50099 : List (Nat × Nat × Nat) := [(6570588160,111681607424144,111681994560315)]
theorem point_links_checked50099 : (cuts50099.take 1).map (fun c => (6570508289-1+2*2^10*c.k,111681457659430+c.lower,111681844795520+c.upper)) = pointBounds50099 := by
 decide +kernel
def cuts50100 : List PrefixCut := [⟨64,248588051,248588191⟩]
theorem checked50100 : checkPrefixCuts (2^48) 6570639361 10 Manual.Count131072.C050100.packed 64 cuts50100 = true := by
 decide +kernel
def cuts50101 : List PrefixCut := [⟨12,45707450,45707477⟩,
⟨64,245670195,245670332⟩]
theorem checked50101 : checkPrefixCuts (2^48) 6570770433 10 Manual.Count131072.C050101.packed 64 cuts50101 = true := by
 decide +kernel
def pointBounds50101 : List (Nat × Nat × Nat) := [(6570795008,111681996606817,111682383743209)]
theorem point_links_checked50101 : (cuts50101.take 1).map (fun c => (6570770433-1+2*2^10*c.k,111681950899367+c.lower,111682338035732+c.upper)) = pointBounds50101 := by
 decide +kernel
def cuts50102 : List PrefixCut := [⟨49,190321440,190321552⟩,
⟨64,249520538,249520683⟩]
theorem checked50102 : checkPrefixCuts (2^48) 6570901505 10 Manual.Count131072.C050102.packed 64 cuts50102 = true := by
 decide +kernel
def pointBounds50102 : List (Nat × Nat × Nat) := [(6571001856,111682386891002,111682774027616)]
theorem point_links_checked50102 : (cuts50102.take 1).map (fun c => (6570901505-1+2*2^10*c.k,111682196569562+c.lower,111682583706064+c.upper)) = pointBounds50102 := by
 decide +kernel
def cuts50103 : List PrefixCut := [⟨64,249301363,249301508⟩]
theorem checked50103 : checkPrefixCuts (2^48) 6571032577 10 Manual.Count131072.C050103.packed 64 cuts50103 = true := by
 decide +kernel
def cuts50104 : List PrefixCut := [⟨22,83185021,83185070⟩,
⟨64,246854840,246854982⟩]
theorem checked50104 : checkPrefixCuts (2^48) 6571163649 10 Manual.Count131072.C050104.packed 64 cuts50104 = true := by
 decide +kernel
def pointBounds50104 : List (Nat × Nat × Nat) := [(6571208704,111682778576484,111683165713325)]
theorem point_links_checked50104 : (cuts50104.take 1).map (fun c => (6571163649-1+2*2^10*c.k,111682695391463+c.lower,111683082528255+c.upper)) = pointBounds50104 := by
 decide +kernel
def cuts50105 : List PrefixCut := [⟨59,228003306,228003439⟩,
⟨64,247192575,247192718⟩]
theorem checked50105 : checkPrefixCuts (2^48) 6571294721 10 Manual.Count131072.C050105.packed 64 cuts50105 = true := by
 decide +kernel
def pointBounds50105 : List (Nat × Nat × Nat) := [(6571415552,111683170249609,111683557386676)]
theorem point_links_checked50105 : (cuts50105.take 1).map (fun c => (6571294721-1+2*2^10*c.k,111682942246303+c.lower,111683329383237+c.upper)) = pointBounds50105 := by
 decide +kernel
def cuts50106 : List PrefixCut := [⟨64,249500629,249500769⟩]
theorem checked50106 : checkPrefixCuts (2^48) 6571425793 10 Manual.Count131072.C050106.packed 64 cuts50106 = true := by
 decide +kernel
def cuts50107 : List PrefixCut := [⟨32,124898367,124898436⟩,
⟨64,248167883,248168022⟩]
theorem checked50107 : checkPrefixCuts (2^48) 6571556865 10 Manual.Count131072.C050107.packed 64 cuts50107 = true := by
 decide +kernel
def pointBounds50107 : List (Nat × Nat × Nat) := [(6571622400,111683563837874,111683950975160)]
theorem point_links_checked50107 : (cuts50107.take 1).map (fun c => (6571556865-1+2*2^10*c.k,111683438939507+c.lower,111683826076724+c.upper)) = pointBounds50107 := by
 decide +kernel
def cuts50108 : List PrefixCut := [⟨64,248377065,248377203⟩]
theorem checked50108 : checkPrefixCuts (2^48) 6571687937 10 Manual.Count131072.C050108.packed 64 cuts50108 = true := by
 decide +kernel
def cuts50109 : List PrefixCut := [⟨5,17731850,17731862⟩,
⟨64,248928879,248929028⟩]
theorem checked50109 : checkPrefixCuts (2^48) 6571819009 10 Manual.Count131072.C050109.packed 64 cuts50109 = true := by
 decide +kernel
def pointBounds50109 : List (Nat × Nat × Nat) := [(6571829248,111683953216305,111684340353811)]
theorem point_links_checked50109 : (cuts50109.take 1).map (fun c => (6571819009-1+2*2^10*c.k,111683935484455+c.lower,111684322621949+c.upper)) = pointBounds50109 := by
 decide +kernel
def cuts50110 : List PrefixCut := [⟨42,165021902,165021991⟩,
⟨64,251536541,251536678⟩]
theorem checked50110 : checkPrefixCuts (2^48) 6571950081 10 Manual.Count131072.C050110.packed 64 cuts50110 = true := by
 decide +kernel
def pointBounds50110 : List (Nat × Nat × Nat) := [(6572036096,111684349435236,111684736572968)]
theorem point_links_checked50110 : (cuts50110.take 1).map (fun c => (6571950081-1+2*2^10*c.k,111684184413334+c.lower,111684571550977+c.upper)) = pointBounds50110 := by
 decide +kernel
def cuts50111 : List PrefixCut := [⟨64,248576368,248576509⟩]
theorem checked50111 : checkPrefixCuts (2^48) 6572081153 10 Manual.Count131072.C050111.packed 64 cuts50111 = true := by
 decide +kernel
def cuts50112 : List PrefixCut := [⟨15,58417296,58417327⟩,
⟨64,250327352,250327491⟩]
theorem checked50112 : checkPrefixCuts (2^48) 6572212225 10 Manual.Count131072.C050112.packed 64 cuts50112 = true := by
 decide +kernel
def pointBounds50112 : List (Nat × Nat × Nat) := [(6572242944,111684742943539,111685130081491)]
theorem point_links_checked50112 : (cuts50112.take 1).map (fun c => (6572212225-1+2*2^10*c.k,111684684526243+c.lower,111685071664164+c.upper)) = pointBounds50112 := by
 decide +kernel
def cuts50113 : List PrefixCut := [⟨52,204669421,204669535⟩,
⟨64,251692810,251692949⟩]
theorem checked50113 : checkPrefixCuts (2^48) 6572343297 10 Manual.Count131072.C050113.packed 64 cuts50113 = true := by
 decide +kernel
def pointBounds50113 : List (Nat × Nat × Nat) := [(6572449792,111685139523016,111685526661190)]
theorem point_links_checked50113 : (cuts50113.take 1).map (fun c => (6572343297-1+2*2^10*c.k,111684934853595+c.lower,111685321991655+c.upper)) = pointBounds50113 := by
 decide +kernel
def cuts50114 : List PrefixCut := [⟨64,246934098,246934239⟩]
theorem checked50114 : checkPrefixCuts (2^48) 6572474369 10 Manual.Count131072.C050114.packed 64 cuts50114 = true := by
 decide +kernel
def cuts50115 : List PrefixCut := [⟨25,94729564,94729616⟩,
⟨64,245858538,245858676⟩]
theorem checked50115 : checkPrefixCuts (2^48) 6572605441 10 Manual.Count131072.C050115.packed 64 cuts50115 = true := by
 decide +kernel
def pointBounds50115 : List (Nat × Nat × Nat) := [(6572656640,111685528210067,111685915348459)]
theorem point_links_checked50115 : (cuts50115.take 1).map (fun c => (6572605441-1+2*2^10*c.k,111685433480503+c.lower,111685820618843+c.upper)) = pointBounds50115 := by
 decide +kernel
def cuts50116 : List PrefixCut := [⟨62,238702094,238702229⟩,
⟨64,246667316,246667455⟩]
theorem checked50116 : checkPrefixCuts (2^48) 6572736513 10 Manual.Count131072.C050116.packed 64 cuts50116 = true := by
 decide +kernel
def pointBounds50116 : List (Nat × Nat × Nat) := [(6572863488,111685918041135,111686305179748)]
theorem point_links_checked50116 : (cuts50116.take 1).map (fun c => (6572736513-1+2*2^10*c.k,111685679339041+c.lower,111686066477519+c.upper)) = pointBounds50116 := by
 decide +kernel
def cuts50117 : List PrefixCut := [⟨64,251544260,251544405⟩]
theorem checked50117 : checkPrefixCuts (2^48) 6572867585 10 Manual.Count131072.C050117.packed 64 cuts50117 = true := by
 decide +kernel
def cuts50118 : List PrefixCut := [⟨35,139430619,139430696⟩,
⟨64,252224413,252224552⟩]
theorem checked50118 : checkPrefixCuts (2^48) 6572998657 10 Manual.Count131072.C050118.packed 64 cuts50118 = true := by
 decide +kernel
def pointBounds50118 : List (Nat × Nat × Nat) := [(6573070336,111686316981236,111686704120075)]
theorem point_links_checked50118 : (cuts50118.take 1).map (fun c => (6572998657-1+2*2^10*c.k,111686177550617+c.lower,111686564689379+c.upper)) = pointBounds50118 := by
 decide +kernel
def cuts50119 : List PrefixCut := [⟨64,250463702,250463849⟩]
theorem checked50119 : checkPrefixCuts (2^48) 6573129729 10 Manual.Count131072.C050119.packed 64 cuts50119 = true := by
 decide +kernel
def cuts50120 : List PrefixCut := [⟨8,30959687,30959705⟩,
⟨64,253370480,253370624⟩]
theorem checked50120 : checkPrefixCuts (2^48) 6573260801 10 Manual.Count131072.C050120.packed 64 cuts50120 = true := by
 decide +kernel
def pointBounds50120 : List (Nat × Nat × Nat) := [(6573277184,111686711198419,111687098337485)]
theorem point_links_checked50120 : (cuts50120.take 1).map (fun c => (6573260801-1+2*2^10*c.k,111686680238732+c.lower,111687067377780+c.upper)) = pointBounds50120 := by
 decide +kernel
def cuts50121 : List PrefixCut := [⟨45,174919874,174919973⟩,
⟨64,249468828,249468969⟩]
theorem checked50121 : checkPrefixCuts (2^48) 6573391873 10 Manual.Count131072.C050121.packed 64 cuts50121 = true := by
 decide +kernel
def pointBounds50121 : List (Nat × Nat × Nat) := [(6573484032,111687108529086,111687495668377)]
theorem point_links_checked50121 : (cuts50121.take 1).map (fun c => (6573391873-1+2*2^10*c.k,111686933609212+c.lower,111687320748404+c.upper)) = pointBounds50121 := by
 decide +kernel
def cuts50122 : List PrefixCut := [⟨64,246380893,246381035⟩]
theorem checked50122 : checkPrefixCuts (2^48) 6573522945 10 Manual.Count131072.C050122.packed 64 cuts50122 = true := by
 decide +kernel
def cuts50123 : List PrefixCut := [⟨18,69023446,69023485⟩,
⟨64,246975420,246975562⟩]
theorem checked50123 : checkPrefixCuts (2^48) 6573654017 10 Manual.Count131072.C050123.packed 64 cuts50123 = true := by
 decide +kernel
def pointBounds50123 : List (Nat × Nat × Nat) := [(6573690880,111687498482379,111687885621893)]
theorem point_links_checked50123 : (cuts50123.take 1).map (fun c => (6573654017-1+2*2^10*c.k,111687429458933+c.lower,111687816598408+c.upper)) = pointBounds50123 := by
 decide +kernel
def cuts50124 : List PrefixCut := [⟨55,217469684,217469807⟩,
⟨64,251038202,251038345⟩]
theorem checked50124 : checkPrefixCuts (2^48) 6573785089 10 Manual.Count131072.C050124.packed 64 cuts50124 = true := by
 decide +kernel
def pointBounds50124 : List (Nat × Nat × Nat) := [(6573897728,111687893904037,111688281043777)]
theorem point_links_checked50124 : (cuts50124.take 1).map (fun c => (6573785089-1+2*2^10*c.k,111687676434353+c.lower,111688063573970+c.upper)) = pointBounds50124 := by
 decide +kernel
def cuts50125 : List PrefixCut := [⟨64,246451768,246451911⟩]
theorem checked50125 : checkPrefixCuts (2^48) 6573916161 10 Manual.Count131072.C050125.packed 64 cuts50125 = true := by
 decide +kernel
def cuts50126 : List PrefixCut := [⟨28,108837985,108838044⟩,
⟨64,248373581,248373717⟩]
theorem checked50126 : checkPrefixCuts (2^48) 6574047233 10 Manual.Count131072.C050126.packed 64 cuts50126 = true := by
 decide +kernel
def pointBounds50126 : List (Nat × Nat × Nat) := [(6574104576,111688282762308,111688669902270)]
theorem point_links_checked50126 : (cuts50126.take 1).map (fun c => (6574047233-1+2*2^10*c.k,111688173924323+c.lower,111688561064226+c.upper)) = pointBounds50126 := by
 decide +kernel
def cuts50127 : List PrefixCut := [⟨64,245200313,245200449⟩]
theorem checked50127 : checkPrefixCuts (2^48) 6574178305 10 Manual.Count131072.C050127.packed 64 cuts50127 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000003
