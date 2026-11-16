import PlattPointSubsetKernel
import PlattPointPackets.S2B000243
import PlattPointPackets.S2B000244
import PlattPointPackets.S2B000245
import PlattPointPackets.S2B000246
import PlattPointPackets.S2B000247
import PlattGlobalGrid.S7B000053
namespace ChenEffective.PlattWindow.PointCovers.S7B000053
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000243.points ++ ChenEffective.PlattWindow.PointPackets.S2B000244.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000245.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000246.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000247.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000053.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000053.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000053
