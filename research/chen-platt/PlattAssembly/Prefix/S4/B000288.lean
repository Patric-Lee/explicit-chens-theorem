import PlattAssemblyKernel
import PlattCertificates.Count131072.C039216
import PlattCertificates.Count131072.C039217
import PlattCertificates.Count131072.C039218
import PlattCertificates.Count131072.C039219
import PlattCertificates.Count131072.C039220
import PlattCertificates.Count131072.C039221
import PlattCertificates.Count131072.C039222
import PlattCertificates.Count131072.C039223
import PlattCertificates.Count131072.C039224
import PlattCertificates.Count131072.C039225
import PlattCertificates.Count131072.C039226
import PlattCertificates.Count131072.C039227
import PlattCertificates.Count131072.C039228
import PlattCertificates.Count131072.C039229
import PlattCertificates.Count131072.C039230
import PlattCertificates.Count131072.C039231
import PlattCertificates.Count131072.C039232
import PlattCertificates.Count131072.C039233
import PlattCertificates.Count131072.C039234
import PlattCertificates.Count131072.C039235
import PlattCertificates.Count131072.C039236
import PlattCertificates.Count131072.C039237
import PlattCertificates.Count131072.C039238
import PlattCertificates.Count131072.C039239
import PlattCertificates.Count131072.C039240
import PlattCertificates.Count131072.C039241
import PlattCertificates.Count131072.C039242
import PlattCertificates.Count131072.C039243
import PlattCertificates.Count131072.C039244
import PlattCertificates.Count131072.C039245
import PlattCertificates.Count131072.C039246
import PlattCertificates.Count131072.C039247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000288
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39216 : List PrefixCut := [⟨64,317418083,317418274⟩]
theorem checked39216 : checkPrefixCuts (2^48) 5144051713 10 Manual.Count131072.C039216.packed 64 cuts39216 = true := by
 decide +kernel
def cuts39217 : List PrefixCut := [⟨2,9466059,9466065⟩,
⟨64,320966564,320966757⟩]
theorem checked39217 : checkPrefixCuts (2^48) 5144182785 10 Manual.Count131072.C039217.packed 64 cuts39217 = true := by
 decide +kernel
def pointBounds39217 : List (Nat × Nat × Nat) := [(5144186880,108617676900967,108618062258539)]
theorem point_links_checked39217 : (cuts39217.take 1).map (fun c => (5144182785-1+2*2^10*c.k,108617667434908+c.lower,108618052792474+c.upper)) = pointBounds39217 := by
 decide +kernel
def cuts39218 : List PrefixCut := [⟨17,83878936,83878989⟩,
⟨64,316964198,316964390⟩]
theorem checked39218 : checkPrefixCuts (2^48) 5144313857 10 Manual.Count131072.C039218.packed 64 cuts39218 = true := by
 decide +kernel
def pointBounds39218 : List (Nat × Nat × Nat) := [(5144348672,108618072280408,108618457638220)]
theorem point_links_checked39218 : (cuts39218.take 1).map (fun c => (5144313857-1+2*2^10*c.k,108617988401472+c.lower,108618373759231+c.upper)) = pointBounds39218 := by
 decide +kernel
def cuts39219 : List PrefixCut := [⟨32,159928982,159929078⟩,
⟨64,320676629,320676819⟩]
theorem checked39219 : checkPrefixCuts (2^48) 5144444929 10 Manual.Count131072.C039219.packed 64 cuts39219 = true := by
 decide +kernel
def pointBounds39219 : List (Nat × Nat × Nat) := [(5144510464,108618465294652,108618850652699)]
theorem point_links_checked39219 : (cuts39219.take 1).map (fun c => (5144444929-1+2*2^10*c.k,108618305365670+c.lower,108618690723621+c.upper)) = pointBounds39219 := by
 decide +kernel
def cuts39220 : List PrefixCut := [⟨47,234935181,234935319⟩,
⟨64,322528674,322528862⟩]
theorem checked39220 : checkPrefixCuts (2^48) 5144576001 10 Manual.Count131072.C039220.packed 64 cuts39220 = true := by
 decide +kernel
def pointBounds39220 : List (Nat × Nat × Nat) := [(5144672256,108618860977480,108619246335759)]
theorem point_links_checked39220 : (cuts39220.take 1).map (fun c => (5144576001-1+2*2^10*c.k,108618626042299+c.lower,108619011400440+c.upper)) = pointBounds39220 := by
 decide +kernel
def cuts39221 : List PrefixCut := [⟨62,308842877,308843060⟩,
⟨64,319073680,319073869⟩]
theorem checked39221 : checkPrefixCuts (2^48) 5144707073 10 Manual.Count131072.C039221.packed 64 cuts39221 = true := by
 decide +kernel
def pointBounds39221 : List (Nat × Nat × Nat) := [(5144834048,108619257413850,108619642772362)]
theorem point_links_checked39221 : (cuts39221.take 1).map (fun c => (5144707073-1+2*2^10*c.k,108618948570973+c.lower,108619333929302+c.upper)) = pointBounds39221 := by
 decide +kernel
def cuts39222 : List PrefixCut := [⟨64,323387575,323387765⟩]
theorem checked39222 : checkPrefixCuts (2^48) 5144838145 10 Manual.Count131072.C039222.packed 64 cuts39222 = true := by
 decide +kernel
def cuts39223 : List PrefixCut := [⟨13,65322091,65322129⟩,
⟨64,322558762,322558956⟩]
theorem checked39223 : checkPrefixCuts (2^48) 5144969217 10 Manual.Count131072.C039223.packed 64 cuts39223 = true := by
 decide +kernel
def pointBounds39223 : List (Nat × Nat × Nat) := [(5144995840,108619656354319,108620041713065)]
theorem point_links_checked39223 : (cuts39223.take 1).map (fun c => (5144969217-1+2*2^10*c.k,108619591032228+c.lower,108619976390936+c.upper)) = pointBounds39223 := by
 decide +kernel
def cuts39224 : List PrefixCut := [⟨28,140925394,140925480⟩,
⟨64,319596394,319596587⟩]
theorem checked39224 : checkPrefixCuts (2^48) 5145100289 10 Manual.Count131072.C039224.packed 64 cuts39224 = true := by
 decide +kernel
def pointBounds39224 : List (Nat × Nat × Nat) := [(5145157632,108620054516384,108620439875372)]
theorem point_links_checked39224 : (cuts39224.take 1).map (fun c => (5145100289-1+2*2^10*c.k,108619913590990+c.lower,108620298949892+c.upper)) = pointBounds39224 := by
 decide +kernel
def cuts39225 : List PrefixCut := [⟨43,218767305,218767435⟩,
⟨64,325332276,325332471⟩]
theorem checked39225 : checkPrefixCuts (2^48) 5145231361 10 Manual.Count131072.C039225.packed 64 cuts39225 = true := by
 decide +kernel
def pointBounds39225 : List (Nat × Nat × Nat) := [(5145319424,108620451954689,108620837313914)]
theorem point_links_checked39225 : (cuts39225.take 1).map (fun c => (5145231361-1+2*2^10*c.k,108620233187384+c.lower,108620618546479+c.upper)) = pointBounds39225 := by
 decide +kernel
def cuts39226 : List PrefixCut := [⟨58,290860927,290861099⟩,
⟨64,320236573,320236763⟩]
theorem checked39226 : checkPrefixCuts (2^48) 5145362433 10 Manual.Count131072.C039226.packed 64 cuts39226 = true := by
 decide +kernel
def pointBounds39226 : List (Nat × Nat × Nat) := [(5145481216,108620849380587,108621234740049)]
theorem point_links_checked39226 : (cuts39226.take 1).map (fun c => (5145362433-1+2*2^10*c.k,108620558519660+c.lower,108620943878950+c.upper)) = pointBounds39226 := by
 decide +kernel
def cuts39227 : List PrefixCut := [⟨64,317985605,317985798⟩]
theorem checked39227 : checkPrefixCuts (2^48) 5145493505 10 Manual.Count131072.C039227.packed 64 cuts39227 = true := by
 decide +kernel
def cuts39228 : List PrefixCut := [⟨9,46934054,46934083⟩,
⟨64,319892070,319892265⟩]
theorem checked39228 : checkPrefixCuts (2^48) 5145624577 10 Manual.Count131072.C039228.packed 64 cuts39228 = true := by
 decide +kernel
def pointBounds39228 : List (Nat × Nat × Nat) := [(5145643008,108621243675892,108621629035594)]
theorem point_links_checked39228 : (cuts39228.take 1).map (fun c => (5145624577-1+2*2^10*c.k,108621196741838+c.lower,108621582101511+c.upper)) = pointBounds39228 := by
 decide +kernel
def cuts39229 : List PrefixCut := [⟨24,119902707,119902777⟩,
⟨64,317805288,317805475⟩]
theorem checked39229 : checkPrefixCuts (2^48) 5145755649 10 Manual.Count131072.C039229.packed 64 cuts39229 = true := by
 decide +kernel
def pointBounds39229 : List (Nat × Nat × Nat) := [(5145804800,108621636536615,108622021896553)]
theorem point_links_checked39229 : (cuts39229.take 1).map (fun c => (5145755649-1+2*2^10*c.k,108621516633908+c.lower,108621901993776+c.upper)) = pointBounds39229 := by
 decide +kernel
def cuts39230 : List PrefixCut := [⟨39,193523586,193523701⟩,
⟨64,319383424,319383616⟩]
theorem checked39230 : checkPrefixCuts (2^48) 5145886721 10 Manual.Count131072.C039230.packed 64 cuts39230 = true := by
 decide +kernel
def pointBounds39230 : List (Nat × Nat × Nat) := [(5145966592,108622027962782,108622413322952)]
theorem point_links_checked39230 : (cuts39230.take 1).map (fun c => (5145886721-1+2*2^10*c.k,108621834439196+c.lower,108622219799251+c.upper)) = pointBounds39230 := by
 decide +kernel
def cuts39231 : List PrefixCut := [⟨54,270093922,270094089⟩,
⟨64,318226691,318226887⟩]
theorem checked39231 : checkPrefixCuts (2^48) 5146017793 10 Manual.Count131072.C039231.packed 64 cuts39231 = true := by
 decide +kernel
def pointBounds39231 : List (Nat × Nat × Nat) := [(5146128384,108622423916542,108622809276956)]
theorem point_links_checked39231 : (cuts39231.take 1).map (fun c => (5146017793-1+2*2^10*c.k,108622153822620+c.lower,108622539182867+c.upper)) = pointBounds39231 := by
 decide +kernel
def cuts39232 : List PrefixCut := [⟨64,321664390,321664581⟩]
theorem checked39232 : checkPrefixCuts (2^48) 5146148865 10 Manual.Count131072.C039232.packed 64 cuts39232 = true := by
 decide +kernel
def cuts39233 : List PrefixCut := [⟨5,24940818,24940833⟩,
⟨64,318757393,318757581⟩]
theorem checked39233 : checkPrefixCuts (2^48) 5146279937 10 Manual.Count131072.C039233.packed 64 cuts39233 = true := by
 decide +kernel
def pointBounds39233 : List (Nat × Nat × Nat) := [(5146290176,108622818654519,108623204015168)]
theorem point_links_checked39233 : (cuts39233.take 1).map (fun c => (5146279937-1+2*2^10*c.k,108622793713701+c.lower,108623179074335+c.upper)) = pointBounds39233 := by
 decide +kernel
def cuts39234 : List PrefixCut := [⟨20,99924502,99924562⟩,
⟨64,321812038,321812233⟩]
theorem checked39234 : checkPrefixCuts (2^48) 5146411009 10 Manual.Count131072.C039234.packed 64 cuts39234 = true := by
 decide +kernel
def pointBounds39234 : List (Nat × Nat × Nat) := [(5146451968,108623212395596,108623597756478)]
theorem point_links_checked39234 : (cuts39234.take 1).map (fun c => (5146411009-1+2*2^10*c.k,108623112471094+c.lower,108623497831916+c.upper)) = pointBounds39234 := by
 decide +kernel
def cuts39235 : List PrefixCut := [⟨35,173481967,173482072⟩,
⟨64,321202261,321202456⟩]
theorem checked39235 : checkPrefixCuts (2^48) 5146542081 10 Manual.Count131072.C039235.packed 64 cuts39235 = true := by
 decide +kernel
def pointBounds39235 : List (Nat × Nat × Nat) := [(5146613760,108623607765099,108623993126221)]
theorem point_links_checked39235 : (cuts39235.take 1).map (fun c => (5146542081-1+2*2^10*c.k,108623434283132+c.lower,108623819644149+c.upper)) = pointBounds39235 := by
 decide +kernel
def cuts39236 : List PrefixCut := [⟨50,249168113,249168260⟩,
⟨64,321412819,321413009⟩]
theorem checked39236 : checkPrefixCuts (2^48) 5146673153 10 Manual.Count131072.C039236.packed 64 cuts39236 = true := by
 decide +kernel
def pointBounds39236 : List (Nat × Nat × Nat) := [(5146775552,108624004653506,108624390014865)]
theorem point_links_checked39236 : (cuts39236.take 1).map (fun c => (5146673153-1+2*2^10*c.k,108623755485393+c.lower,108624140846605+c.upper)) = pointBounds39236 := by
 decide +kernel
def cuts39237 : List PrefixCut := [⟨64,316045132,316045320⟩]
theorem checked39237 : checkPrefixCuts (2^48) 5146804225 10 Manual.Count131072.C039237.packed 64 cuts39237 = true := by
 decide +kernel
def cuts39238 : List PrefixCut := [⟨1,4921907,4921910⟩,
⟨64,323802744,323802935⟩]
theorem checked39238 : checkPrefixCuts (2^48) 5146935297 10 Manual.Count131072.C039238.packed 64 cuts39238 = true := by
 decide +kernel
def pointBounds39238 : List (Nat × Nat × Nat) := [(5146937344,108624397865251,108624783226844)]
theorem point_links_checked39238 : (cuts39238.take 1).map (fun c => (5146935297-1+2*2^10*c.k,108624392943344+c.lower,108624778304934+c.upper)) = pointBounds39238 := by
 decide +kernel
def cuts39239 : List PrefixCut := [⟨16,78474832,78474881⟩,
⟨64,320294531,320294726⟩]
theorem checked39239 : checkPrefixCuts (2^48) 5147066369 10 Manual.Count131072.C039239.packed 64 cuts39239 = true := by
 decide +kernel
def pointBounds39239 : List (Nat × Nat × Nat) := [(5147099136,108624795220920,108625180582750)]
theorem point_links_checked39239 : (cuts39239.take 1).map (fun c => (5147066369-1+2*2^10*c.k,108624716746088+c.lower,108625102107869+c.upper)) = pointBounds39239 := by
 decide +kernel
def cuts39240 : List PrefixCut := [⟨31,154867182,154867274⟩,
⟨64,318153741,318153930⟩]
theorem checked39240 : checkPrefixCuts (2^48) 5147197441 10 Manual.Count131072.C039240.packed 64 cuts39240 = true := by
 decide +kernel
def pointBounds39240 : List (Nat × Nat × Nat) := [(5147260928,108625191907801,108625577269869)]
theorem point_links_checked39240 : (cuts39240.take 1).map (fun c => (5147197441-1+2*2^10*c.k,108625037040619+c.lower,108625422402595+c.upper)) = pointBounds39240 := by
 decide +kernel
def cuts39241 : List PrefixCut := [⟨46,227536750,227536886⟩,
⟨64,318036267,318036459⟩]
theorem checked39241 : checkPrefixCuts (2^48) 5147328513 10 Manual.Count131072.C039241.packed 64 cuts39241 = true := by
 decide +kernel
def pointBounds39241 : List (Nat × Nat × Nat) := [(5147422720,108625582731110,108625968093411)]
theorem point_links_checked39241 : (cuts39241.take 1).map (fun c => (5147328513-1+2*2^10*c.k,108625355194360+c.lower,108625740556525+c.upper)) = pointBounds39241 := by
 decide +kernel
def cuts39242 : List PrefixCut := [⟨61,307529475,307529654⟩,
⟨64,322348007,322348195⟩]
theorem checked39242 : checkPrefixCuts (2^48) 5147459585 10 Manual.Count131072.C039242.packed 64 cuts39242 = true := by
 decide +kernel
def pointBounds39242 : List (Nat × Nat × Nat) := [(5147584512,108625980760102,108626366122638)]
theorem point_links_checked39242 : (cuts39242.take 1).map (fun c => (5147459585-1+2*2^10*c.k,108625673230627+c.lower,108626058592984+c.upper)) = pointBounds39242 := by
 decide +kernel
def cuts39243 : List PrefixCut := [⟨64,323542780,323542974⟩]
theorem checked39243 : checkPrefixCuts (2^48) 5147590657 10 Manual.Count131072.C039243.packed 64 cuts39243 = true := by
 decide +kernel
def cuts39244 : List PrefixCut := [⟨12,60366031,60366068⟩,
⟨64,321894172,321894367⟩]
theorem checked39244 : checkPrefixCuts (2^48) 5147721729 10 Manual.Count131072.C039244.packed 64 cuts39244 = true := by
 decide +kernel
def pointBounds39244 : List (Nat × Nat × Nat) := [(5147746304,108626379487445,108626764850221)]
theorem point_links_checked39244 : (cuts39244.take 1).map (fun c => (5147721729-1+2*2^10*c.k,108626319121414+c.lower,108626704484153+c.upper)) = pointBounds39244 := by
 decide +kernel
def cuts39245 : List PrefixCut := [⟨27,134124695,134124779⟩,
⟨64,323690300,323690499⟩]
theorem checked39245 : checkPrefixCuts (2^48) 5147852801 10 Manual.Count131072.C039245.packed 64 cuts39245 = true := by
 decide +kernel
def pointBounds39245 : List (Nat × Nat × Nat) := [(5147908096,108626775140281,108627160503299)]
theorem point_links_checked39245 : (cuts39245.take 1).map (fun c => (5147852801-1+2*2^10*c.k,108626641015586+c.lower,108627026378520+c.upper)) = pointBounds39245 := by
 decide +kernel
def cuts39246 : List PrefixCut := [⟨42,209464769,209464897⟩,
⟨64,318323823,318324018⟩]
theorem checked39246 : checkPrefixCuts (2^48) 5147983873 10 Manual.Count131072.C039246.packed 64 cuts39246 = true := by
 decide +kernel
def pointBounds39246 : List (Nat × Nat × Nat) := [(5148069888,108627174170655,108627559533916)]
theorem point_links_checked39246 : (cuts39246.take 1).map (fun c => (5147983873-1+2*2^10*c.k,108626964705886+c.lower,108627350069019+c.upper)) = pointBounds39246 := by
 decide +kernel
def cuts39247 : List PrefixCut := [⟨57,288518435,288518606⟩,
⟨64,325314047,325314240⟩]
theorem checked39247 : checkPrefixCuts (2^48) 5148114945 10 Manual.Count131072.C039247.packed 64 cuts39247 = true := by
 decide +kernel
def pointBounds39247 : List (Nat × Nat × Nat) := [(5148231680,108627571548144,108627956911643)]
theorem point_links_checked39247 : (cuts39247.take 1).map (fun c => (5148114945-1+2*2^10*c.k,108627283029709+c.lower,108627668393037+c.upper)) = pointBounds39247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000288
