import PlattAssemblyKernel
import PlattCertificates.Count131072.C022144
import PlattCertificates.Count131072.C022145
import PlattCertificates.Count131072.C022146
import PlattCertificates.Count131072.C022147
import PlattCertificates.Count131072.C022148
import PlattCertificates.Count131072.C022149
import PlattCertificates.Count131072.C022150
import PlattCertificates.Count131072.C022151
import PlattCertificates.Count131072.C022152
import PlattCertificates.Count131072.C022153
import PlattCertificates.Count131072.C022154
import PlattCertificates.Count131072.C022155
import PlattCertificates.Count131072.C022156
import PlattCertificates.Count131072.C022157
import PlattCertificates.Count131072.C022158
import PlattCertificates.Count131072.C022159
import PlattCertificates.Count131072.C022160
import PlattCertificates.Count131072.C022161
import PlattCertificates.Count131072.C022162
import PlattCertificates.Count131072.C022163
import PlattCertificates.Count131072.C022164
import PlattCertificates.Count131072.C022165
import PlattCertificates.Count131072.C022166
import PlattCertificates.Count131072.C022167
import PlattCertificates.Count131072.C022168
import PlattCertificates.Count131072.C022169
import PlattCertificates.Count131072.C022170
import PlattCertificates.Count131072.C022171
import PlattCertificates.Count131072.C022172
import PlattCertificates.Count131072.C022173
import PlattCertificates.Count131072.C022174
import PlattCertificates.Count131072.C022175
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22144 : List PrefixCut := [⟨36,165994507,165994603⟩,
⟨125,565767109,565767440⟩,
⟨128,578453486,578453825⟩]
theorem checked22144 : checkPrefixCuts (2^48) 2906390529 9 Manual.Count131072.C022144.packed 128 cuts22144 = true := by
 decide +kernel
def pointBounds22144 : List (Nat × Nat × Nat) := [(2906427392,101337618286130,101337999418643),(2906518528,101338018058732,101338399191480)]
theorem point_links_checked22144 : (cuts22144.take 2).map (fun c => (2906390529-1+2*2^9*c.k,101337452291623+c.lower,101337833424040+c.upper)) = pointBounds22144 := by
 decide +kernel
def cuts22145 : List PrefixCut := [⟨86,392787359,392787584⟩,
⟨128,582688413,582688746⟩]
theorem checked22145 : checkPrefixCuts (2^48) 2906521601 9 Manual.Count131072.C022145.packed 128 cuts22145 = true := by
 decide +kernel
def pointBounds22145 : List (Nat × Nat × Nat) := [(2906609664,101338423532468,101338804665449)]
theorem point_links_checked22145 : (cuts22145.take 1).map (fun c => (2906521601-1+2*2^9*c.k,101338030745109+c.lower,101338411877865+c.upper)) = pointBounds22145 := by
 decide +kernel
def cuts22146 : List PrefixCut := [⟨47,214978931,214979052⟩,
⟨128,581790620,581790955⟩]
theorem checked22146 : checkPrefixCuts (2^48) 2906652673 9 Manual.Count131072.C022146.packed 128 cuts22146 = true := by
 decide +kernel
def pointBounds22146 : List (Nat × Nat × Nat) := [(2906700800,101338828412453,101339209545663)]
theorem point_links_checked22146 : (cuts22146.take 1).map (fun c => (2906652673-1+2*2^9*c.k,101338613433522+c.lower,101338994566611+c.upper)) = pointBounds22146 := by
 decide +kernel
def cuts22147 : List PrefixCut := [⟨8,34956948,34956968⟩,
⟨97,446396119,446396367⟩,
⟨128,590285431,590285760⟩]
theorem checked22147 : checkPrefixCuts (2^48) 2906783745 9 Manual.Count131072.C022147.packed 128 cuts22147 = true := by
 decide +kernel
def pointBounds22147 : List (Nat × Nat × Nat) := [(2906791936,101339230181090,101339611314534),(2906883072,101339641620261,101340022753933)]
theorem point_links_checked22147 : (cuts22147.take 2).map (fun c => (2906783745-1+2*2^9*c.k,101339195224142+c.lower,101339576357566+c.upper)) = pointBounds22147 := by
 decide +kernel
def cuts22148 : List PrefixCut := [⟨58,268408429,268408585⟩,
⟨128,591324019,591324359⟩]
theorem checked22148 : checkPrefixCuts (2^48) 2906914817 9 Manual.Count131072.C022148.packed 128 cuts22148 = true := by
 decide +kernel
def pointBounds22148 : List (Nat × Nat × Nat) := [(2906974208,101340053918002,101340435051911)]
theorem point_links_checked22148 : (cuts22148.take 1).map (fun c => (2906914817-1+2*2^9*c.k,101339785509573+c.lower,101340166643326+c.upper)) = pointBounds22148 := by
 decide +kernel
def cuts22149 : List PrefixCut := [⟨19,88110515,88110564⟩,
⟨108,501931618,501931896⟩,
⟨128,588683274,588683600⟩]
theorem checked22149 : checkPrefixCuts (2^48) 2907045889 9 Manual.Count131072.C022149.packed 128 cuts22149 = true := by
 decide +kernel
def pointBounds22149 : List (Nat × Nat × Nat) := [(2907065344,101340464944107,101340846078249),(2907156480,101340878765210,101341259899581)]
theorem point_links_checked22149 : (cuts22149.take 2).map (fun c => (2907045889-1+2*2^9*c.k,101340376833592+c.lower,101340757967685+c.upper)) = pointBounds22149 := by
 decide +kernel
def cuts22150 : List PrefixCut := [⟨69,304013295,304013464⟩,
⟨128,572778197,572778523⟩]
theorem checked22150 : checkPrefixCuts (2^48) 2907176961 9 Manual.Count131072.C022150.packed 128 cuts22150 = true := by
 decide +kernel
def pointBounds22150 : List (Nat × Nat × Nat) := [(2907247616,101341269530161,101341650664749)]
theorem point_links_checked22150 : (cuts22150.take 1).map (fun c => (2907176961-1+2*2^9*c.k,101340965516866+c.lower,101341346651285+c.upper)) = pointBounds22150 := by
 decide +kernel
def cuts22151 : List PrefixCut := [⟨30,134283546,134283624⟩,
⟨119,538868389,538868702⟩,
⟨128,577593237,577593573⟩]
theorem checked22151 : checkPrefixCuts (2^48) 2907308033 9 Manual.Count131072.C022151.packed 128 cuts22151 = true := by
 decide +kernel
def pointBounds22151 : List (Nat × Nat × Nat) := [(2907338752,101341672578609,101342053713432),(2907429888,101342077163452,101342458298510)]
theorem point_links_checked22151 : (cuts22151.take 2).map (fun c => (2907308033-1+2*2^9*c.k,101341538295063+c.lower,101341919429808+c.upper)) = pointBounds22151 := by
 decide +kernel
def cuts22152 : List PrefixCut := [⟨80,365750526,365750735⟩,
⟨128,582891791,582892130⟩]
theorem checked22152 : checkPrefixCuts (2^48) 2907439105 9 Manual.Count131072.C022152.packed 128 cuts22152 = true := by
 decide +kernel
def pointBounds22152 : List (Nat × Nat × Nat) := [(2907521024,101342481638826,101342862774116)]
theorem point_links_checked22152 : (cuts22152.take 1).map (fun c => (2907439105-1+2*2^9*c.k,101342115888300+c.lower,101342497023381+c.upper)) = pointBounds22152 := by
 decide +kernel
def cuts22153 : List PrefixCut := [⟨41,182674640,182674740⟩,
⟨128,577637928,577638248⟩]
theorem checked22153 : checkPrefixCuts (2^48) 2907570177 9 Manual.Count131072.C022153.packed 128 cuts22153 = true := by
 decide +kernel
def pointBounds22153 : List (Nat × Nat × Nat) := [(2907612160,101342881454731,101343262590251)]
theorem point_links_checked22153 : (cuts22153.take 1).map (fun c => (2907570177-1+2*2^9*c.k,101342698780091+c.lower,101343079915511+c.upper)) = pointBounds22153 := by
 decide +kernel
def cuts22154 : List PrefixCut := [⟨2,8518682,8518687⟩,
⟨91,413730385,413730625⟩,
⟨128,584775121,584775462⟩]
theorem checked22154 : checkPrefixCuts (2^48) 2907701249 9 Manual.Count131072.C022154.packed 128 cuts22154 = true := by
 decide +kernel
def pointBounds22154 : List (Nat × Nat × Nat) := [(2907703296,101343284936701,101343666072446),(2907794432,101343690148404,101344071284384)]
theorem point_links_checked22154 : (cuts22154.take 2).map (fun c => (2907701249-1+2*2^9*c.k,101343276418019+c.lower,101343657553759+c.upper)) = pointBounds22154 := by
 decide +kernel
def cuts22155 : List PrefixCut := [⟨52,239575000,239575134⟩,
⟨128,579134719,579135044⟩]
theorem checked22155 : checkPrefixCuts (2^48) 2907832321 9 Manual.Count131072.C022155.packed 128 cuts22155 = true := by
 decide +kernel
def pointBounds22155 : List (Nat × Nat × Nat) := [(2907885568,101344100768140,101344481904355)]
theorem point_links_checked22155 : (cuts22155.take 1).map (fun c => (2907832321-1+2*2^9*c.k,101343861193140+c.lower,101344242329221+c.upper)) = pointBounds22155 := by
 decide +kernel
def cuts22156 : List PrefixCut := [⟨13,62335522,62335555⟩,
⟨102,466831632,466831903⟩,
⟨128,584916148,584916490⟩]
theorem checked22156 : checkPrefixCuts (2^48) 2907963393 9 Manual.Count131072.C022156.packed 128 cuts22156 = true := by
 decide +kernel
def pointBounds22156 : List (Nat × Nat × Nat) := [(2907976704,101344502663381,101344883799820),(2908067840,101344907159491,101345288296168)]
theorem point_links_checked22156 : (cuts22156.take 2).map (fun c => (2907963393-1+2*2^9*c.k,101344440327859+c.lower,101344821464265+c.upper)) = pointBounds22156 := by
 decide +kernel
def cuts22157 : List PrefixCut := [⟨63,286495654,286495816⟩,
⟨128,578598507,578598841⟩]
theorem checked22157 : checkPrefixCuts (2^48) 2908094465 9 Manual.Count131072.C022157.packed 128 cuts22157 = true := by
 decide +kernel
def pointBounds22157 : List (Nat × Nat × Nat) := [(2908158976,101345311739661,101345692876571)]
theorem point_links_checked22157 : (cuts22157.take 1).map (fun c => (2908094465-1+2*2^9*c.k,101345025244007+c.lower,101345406380755+c.upper)) = pointBounds22157 := by
 decide +kernel
def cuts22158 : List PrefixCut := [⟨24,108883552,108883611⟩,
⟨113,512373723,512374014⟩,
⟨128,581862970,581863301⟩]
theorem checked22158 : checkPrefixCuts (2^48) 2908225537 9 Manual.Count131072.C022158.packed 128 cuts22158 = true := by
 decide +kernel
def pointBounds22158 : List (Nat × Nat × Nat) := [(2908250112,101345712726066,101346093863207),(2908341248,101346116216237,101346497353610)]
theorem point_links_checked22158 : (cuts22158.take 2).map (fun c => (2908225537-1+2*2^9*c.k,101345603842514+c.lower,101345984979596+c.upper)) = pointBounds22158 := by
 decide +kernel
def cuts22159 : List PrefixCut := [⟨74,332149552,332149742⟩,
⟨128,578352747,578353073⟩]
theorem checked22159 : checkPrefixCuts (2^48) 2908356609 9 Manual.Count131072.C022159.packed 128 cuts22159 = true := by
 decide +kernel
def pointBounds22159 : List (Nat × Nat × Nat) := [(2908432384,101346517855036,101346898992639)]
theorem point_links_checked22159 : (cuts22159.take 1).map (fun c => (2908356609-1+2*2^9*c.k,101346185705484+c.lower,101346566842897+c.upper)) = pointBounds22159 := by
 decide +kernel
def cuts22160 : List PrefixCut := [⟨35,158326316,158326404⟩,
⟨124,557036650,557036966⟩,
⟨128,576100886,576101213⟩]
theorem checked22160 : checkPrefixCuts (2^48) 2908487681 9 Manual.Count131072.C022160.packed 128 cuts22160 = true := by
 decide +kernel
def pointBounds22160 : List (Nat × Nat × Nat) := [(2908523520,101346922384547,101347303522374),(2908614656,101347321094881,101347702232936)]
theorem point_links_checked22160 : (cuts22160.take 2).map (fun c => (2908487681-1+2*2^9*c.k,101346764058231+c.lower,101347145195970+c.upper)) = pointBounds22160 := by
 decide +kernel
def cuts22161 : List PrefixCut := [⟨85,386891490,386891719⟩,
⟨128,584106857,584107198⟩]
theorem checked22161 : checkPrefixCuts (2^48) 2908618753 9 Manual.Count131072.C022161.packed 128 cuts22161 = true := by
 decide +kernel
def pointBounds22161 : List (Nat × Nat × Nat) := [(2908705792,101347727050607,101348108188902)]
theorem point_links_checked22161 : (cuts22161.take 1).map (fun c => (2908618753-1+2*2^9*c.k,101347340159117+c.lower,101347721297183+c.upper)) = pointBounds22161 := by
 decide +kernel
def cuts22162 : List PrefixCut := [⟨46,213178922,213179042⟩,
⟨128,587370597,587370931⟩]
theorem checked22162 : checkPrefixCuts (2^48) 2908749825 9 Manual.Count131072.C022162.packed 128 cuts22162 = true := by
 decide +kernel
def pointBounds22162 : List (Nat × Nat × Nat) := [(2908796928,101348137444896,101348518583423)]
theorem point_links_checked22162 : (cuts22162.take 1).map (fun c => (2908749825-1+2*2^9*c.k,101347924265974+c.lower,101348305404381+c.upper)) = pointBounds22162 := by
 decide +kernel
def cuts22163 : List PrefixCut := [⟨7,32319131,32319149⟩,
⟨96,438720475,438720728⟩,
⟨128,580570891,580571225⟩]
theorem checked22163 : checkPrefixCuts (2^48) 2908880897 9 Manual.Count131072.C022163.packed 128 cuts22163 = true := by
 decide +kernel
def pointBounds22163 : List (Nat × Nat × Nat) := [(2908888064,101348543955702,101348925094461),(2908979200,101348950357046,101349331496040)]
theorem point_links_checked22163 : (cuts22163.take 2).map (fun c => (2908880897-1+2*2^9*c.k,101348511636571+c.lower,101348892775312+c.upper)) = pointBounds22163 := by
 decide +kernel
def cuts22164 : List PrefixCut := [⟨57,256990976,256991120⟩,
⟨128,579480310,579480640⟩]
theorem checked22164 : checkPrefixCuts (2^48) 2909011969 9 Manual.Count131072.C022164.packed 128 cuts22164 = true := by
 decide +kernel
def pointBounds22164 : List (Nat × Nat × Nat) := [(2909070336,101349349198438,101349730337657)]
theorem point_links_checked22164 : (cuts22164.take 1).map (fun c => (2909011969-1+2*2^9*c.k,101349092207462+c.lower,101349473346537+c.upper)) = pointBounds22164 := by
 decide +kernel
def cuts22165 : List PrefixCut := [⟨18,81757934,81757982⟩,
⟨107,492958760,492959047⟩,
⟨128,590967783,590968126⟩]
theorem checked22165 : checkPrefixCuts (2^48) 2909143041 9 Manual.Count131072.C022165.packed 128 cuts22165 = true := by
 decide +kernel
def pointBounds22165 : List (Nat × Nat × Nat) := [(2909161472,101349753445706,101350134585159),(2909252608,101350164646532,101350545786224)]
theorem point_links_checked22165 : (cuts22165.take 2).map (fun c => (2909143041-1+2*2^9*c.k,101349671687772+c.lower,101350052827177+c.upper)) = pointBounds22165 := by
 decide +kernel
def cuts22166 : List PrefixCut := [⟨68,307567446,307567619⟩,
⟨128,576041939,576042265⟩]
theorem checked22166 : checkPrefixCuts (2^48) 2909274113 9 Manual.Count131072.C022166.packed 128 cuts22166 = true := by
 decide +kernel
def pointBounds22166 : List (Nat × Nat × Nat) := [(2909343744,101350570223001,101350951362922)]
theorem point_links_checked22166 : (cuts22166.take 1).map (fun c => (2909274113-1+2*2^9*c.k,101350262655555+c.lower,101350643795303+c.upper)) = pointBounds22166 := by
 decide +kernel
def cuts22167 : List PrefixCut := [⟨29,137185903,137185981⟩,
⟨118,542446683,542446993⟩,
⟨128,588592787,588593123⟩]
theorem checked22167 : checkPrefixCuts (2^48) 2909405185 9 Manual.Count131072.C022167.packed 128 cuts22167 = true := by
 decide +kernel
def pointBounds22167 : List (Nat × Nat × Nat) := [(2909434880,101350975883397,101351357023549),(2909526016,101351381144177,101351762284561)]
theorem point_links_checked22167 : (cuts22167.take 2).map (fun c => (2909405185-1+2*2^9*c.k,101350838697494+c.lower,101351219837568+c.upper)) = pointBounds22167 := by
 decide +kernel
def cuts22168 : List PrefixCut := [⟨79,360069375,360069582⟩,
⟨128,580149827,580150163⟩]
theorem checked22168 : checkPrefixCuts (2^48) 2909536257 9 Manual.Count131072.C022168.packed 128 cuts22168 = true := by
 decide +kernel
def pointBounds22168 : List (Nat × Nat × Nat) := [(2909617152,101351787359656,101352168500273)]
theorem point_links_checked22168 : (cuts22168.take 1).map (fun c => (2909536257-1+2*2^9*c.k,101351427290281+c.lower,101351808430691+c.upper)) = pointBounds22168 := by
 decide +kernel
def cuts22169 : List PrefixCut := [⟨40,180027828,180027926⟩,
⟨128,577221680,577222009⟩]
theorem checked22169 : checkPrefixCuts (2^48) 2909667329 9 Manual.Count131072.C022169.packed 128 cuts22169 = true := by
 decide +kernel
def pointBounds22169 : List (Nat × Nat × Nat) := [(2909708288,101352187467936,101352568608780)]
theorem point_links_checked22169 : (cuts22169.take 1).map (fun c => (2909667329-1+2*2^9*c.k,101352007440108+c.lower,101352388580854+c.upper)) = pointBounds22169 := by
 decide +kernel
def cuts22170 : List PrefixCut := [⟨1,4933406,4933409⟩,
⟨90,414109469,414109703⟩,
⟨128,585030971,585031298⟩]
theorem checked22170 : checkPrefixCuts (2^48) 2909798401 9 Manual.Count131072.C022170.packed 128 cuts22170 = true := by
 decide +kernel
def pointBounds22170 : List (Nat × Nat × Nat) := [(2909799424,101352589595194,101352970736272),(2909890560,101352998771257,101353379912566)]
theorem point_links_checked22170 : (cuts22170.take 2).map (fun c => (2909798401-1+2*2^9*c.k,101352584661788+c.lower,101352965802863+c.upper)) = pointBounds22170 := by
 decide +kernel
def cuts22171 : List PrefixCut := [⟨51,235630040,235630175⟩,
⟨128,587132615,587132949⟩]
theorem checked22171 : checkPrefixCuts (2^48) 2909929473 9 Manual.Count131072.C022171.packed 128 cuts22171 = true := by
 decide +kernel
def pointBounds22171 : List (Nat × Nat × Nat) := [(2909981696,101353405322799,101353786464336)]
theorem point_links_checked22171 : (cuts22171.take 1).map (fun c => (2909929473-1+2*2^9*c.k,101353169692759+c.lower,101353550834161+c.upper)) = pointBounds22171 := by
 decide +kernel
def cuts22172 : List PrefixCut := [⟨12,51941082,51941113⟩,
⟨101,455371994,455372261⟩,
⟨128,577240268,577240602⟩]
theorem checked22172 : checkPrefixCuts (2^48) 2910060545 9 Manual.Count131072.C022172.packed 128 cuts22172 = true := by
 decide +kernel
def pointBounds22172 : List (Nat × Nat × Nat) := [(2910072832,101353808766456,101354189908223),(2910163968,101354212197368,101354593339371)]
theorem point_links_checked22172 : (cuts22172.take 2).map (fun c => (2910060545-1+2*2^9*c.k,101353756825374+c.lower,101354137967110+c.upper)) = pointBounds22172 := by
 decide +kernel
def cuts22173 : List PrefixCut := [⟨62,285515580,285515742⟩,
⟨128,588433695,588434034⟩]
theorem checked22173 : checkPrefixCuts (2^48) 2910191617 9 Manual.Count131072.C022173.packed 128 cuts22173 = true := by
 decide +kernel
def pointBounds22173 : List (Nat × Nat × Nat) := [(2910255104,101354619581222,101355000723454)]
theorem point_links_checked22173 : (cuts22173.take 1).map (fun c => (2910191617-1+2*2^9*c.k,101354334065642+c.lower,101354715207712+c.upper)) = pointBounds22173 := by
 decide +kernel
def cuts22174 : List PrefixCut := [⟨23,106774069,106774131⟩,
⟨112,508329531,508329826⟩,
⟨128,580670076,580670413⟩]
theorem checked22174 : checkPrefixCuts (2^48) 2910322689 9 Manual.Count131072.C022174.packed 128 cuts22174 = true := by
 decide +kernel
def pointBounds22174 : List (Nat × Nat × Nat) := [(2910346240,101355029273406,101355410415877),(2910437376,101355430828868,101355811971572)]
theorem point_links_checked22174 : (cuts22174.take 2).map (fun c => (2910322689-1+2*2^9*c.k,101354922499337+c.lower,101355303641746+c.upper)) = pointBounds22174 := by
 decide +kernel
def cuts22175 : List PrefixCut := [⟨73,329782661,329782848⟩,
⟨128,580643909,580644237⟩]
theorem checked22175 : checkPrefixCuts (2^48) 2910453761 9 Manual.Count131072.C022175.packed 128 cuts22175 = true := by
 decide +kernel
def pointBounds22175 : List (Nat × Nat × Nat) := [(2910528512,101355832952074,101356214095007)]
theorem point_links_checked22175 : (cuts22175.take 1).map (fun c => (2910453761-1+2*2^9*c.k,101355503169413+c.lower,101355884312159+c.upper)) = pointBounds22175 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000067
