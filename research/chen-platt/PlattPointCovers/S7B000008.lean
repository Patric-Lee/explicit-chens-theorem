import PlattPointSubsetKernel
import PlattPointPackets.S2B000073
import PlattPointPackets.S2B000074
import PlattPointPackets.S2B000075
import PlattPointPackets.S2B000076
import PlattPointPackets.S2B000077
import PlattGlobalGrid.S7B000008
namespace ChenEffective.PlattWindow.PointCovers.S7B000008
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000073.points ++ ChenEffective.PlattWindow.PointPackets.S2B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000077.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000008.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000008.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000008
