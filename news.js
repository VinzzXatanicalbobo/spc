
(function(){
  async function fetchJSON(src) {
    try {
      // cache-buster ringan supaya update cepat terlihat (opsional)
      const res = await fetch(src + (src.includes('?') ? '&' : '?') + 'v=' + Date.now());
      if (!res.ok) throw new Error('HTTP ' + res.status);
      return await res.json();
    } catch (e) {
      console.warn('NEWS fetch error:', e);
      return [];
    }
  }

  function renderNews(el, items) {
    if (!Array.isArray(items) || !items.length) {
      el.innerHTML = `
        <div class="slide empty">
          <div class="body">
            <h3>Belum ada News</h3>
            <p>Edit file <code>/asset/news.json</code> untuk menambahkan.</p>
          </div>
        </div>`;
      return;
    }

    el.innerHTML = items.map(n => `
      <a class="slide" href="${n.url || '#'}" target="_blank" rel="noopener">
        <div class="pill">News</div>
        <div class="media">
          ${
            n.video
              ? `<video class="vid" src="${n.video}" autoplay muted playsinline loop></video>`
              : `<img alt="" src="${n.img || ''}" />`
          }
        </div>
        <div class="body">
          <h3>${n.title || ''}</h3>
          <p>${n.subtitle || ''}</p>
        </div>
      </a>
    `).join('');

    // Autoplay hanya saat terlihat
    const io = new IntersectionObserver(entries => {
      entries.forEach(e => {
        const m = e.target;
        if (e.isIntersecting) m.play?.().catch(()=>{});
        else m.pause?.();
      });
    }, { threshold: 0.4 });
    el.querySelectorAll('video.vid').forEach(v => io.observe(v));
  }

  // Entry point: jalan di setiap halaman
  document.addEventListener('DOMContentLoaded', async () => {
    const el = document.getElementById('newsSlider');
    if (!el) return; // halaman ini tidak menampilkan news

    // Bisa override sumber JSON per halaman: <div id="newsSlider" data-news-src="/asset/news.json">
    const src = el.getAttribute('data-news-src') || '/asset/news.json';

    // Jika ada override global lewat window.GLOBAL_NEWS, pakai itu.
    if (Array.isArray(window.GLOBAL_NEWS)) {
      renderNews(el, window.GLOBAL_NEWS);
      return;
    }

    const items = await fetchJSON(src);
    renderNews(el, items);
  });
})();
