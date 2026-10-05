// Follow mathematical passages, not percentages of two unrelated documents.
export function choosePaperPassage(blocks, viewport) {
  const line = viewport.top + Math.min(150, (viewport.bottom - viewport.top) * .25);
  const visible = blocks.filter(block => block.bottom > block.top &&
    block.bottom > viewport.top && block.top < viewport.bottom);
  return visible.filter(block => block.top <= line).at(-1) || visible[0] || null;
}

export function createPaperFollower({paper, scroller, isActive, onPassage, onStateChange}) {
  let enabled = true, ready = false, held = false, destination = null;
  let timer = null, lastPassage = null;
  function clearTimer() { clearTimeout(timer); timer = null; }
  function current() {
    const blocks = [...paper.querySelectorAll('.paper-result,.paper-proof[data-proof-of]')]
      .map(element => {
        const box = element.getBoundingClientRect();
        return {id:element.dataset.result || element.dataset.proofOf,
          anchor:element.id, part:element.classList.contains('paper-proof') && element.open ? 'proof' : 'statement',
          top:box.top, bottom:box.bottom};
      }).filter(block => block.id);
    return choosePaperPassage(blocks, scroller.getBoundingClientRect());
  }
  function follow(force = false) {
    clearTimer();
    if (!ready || !enabled || held || !isActive()) return;
    if (destination) {
      const target = destination.getBoundingClientRect().top - scroller.getBoundingClientRect().top + scroller.scrollTop - 32;
      const reachable = Math.max(0, Math.min(target, scroller.scrollHeight - scroller.clientHeight));
      if (Math.abs(scroller.scrollTop - reachable) > 2) return;
      destination = null;
    }
    const passage = current();
    if (!passage) return;
    const key = passage.anchor + ':' + passage.part;
    if (!force && key === lastPassage) return;
    lastPassage = key;
    onPassage(passage, {force});
  }
  function scroll() {
    if (!enabled || held || !isActive()) return;
    // Explicit navigation must reach its destination. A short pause during a
    // long animated jump does not mean the reader chose an intermediate lemma.
    if (timer === null) timer = setTimeout(follow, 90);
  }
  function intent() { held = false; destination = null; }
  scroller.addEventListener('scroll', scroll, {passive:true});
  scroller.addEventListener('wheel', intent, {passive:true});
  scroller.addEventListener('touchmove', intent, {passive:true});
  scroller.addEventListener('pointerdown', intent, {passive:true});
  scroller.addEventListener('keydown', event => {
    if (['ArrowDown','ArrowUp','PageDown','PageUp','Home','End',' '].includes(event.key)) intent();
  });
  return {
    current,
    get enabled() { return enabled; },
    start() { ready = true; },
    hold() { held = true; destination = null; clearTimer(); lastPassage = null; },
    navigate(element) { held = false; destination = element; lastPassage = null; clearTimer(); scroll(); },
    pause() { enabled = false; clearTimer(); onStateChange(false); },
    resume() { enabled = true; held = false; destination = null; onStateChange(true); follow(true); }
  };
}
