import PlattPointSubsetKernel
import PlattPointPackets.S2B000234
import PlattPointPackets.S2B000235
import PlattPointPackets.S2B000236
import PlattPointPackets.S2B000237
import PlattPointPackets.S2B000238
import PlattPointPackets.S2B000239
import PlattGlobalGrid.S7B000051
namespace ChenEffective.PlattWindow.PointCovers.S7B000051
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000234.points ++ ChenEffective.PlattWindow.PointPackets.S2B000235.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000236.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000237.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000238.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000239.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000051.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000051.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000051
